// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "simple_file_watcher.h"

#ifdef __linux__
#include "gracefully_exit.c"

#include <sys/inotify.h>
#include <sys/poll.h>
#include <errno.h>
#include <fcntl.h>
#include <dirent.h>

static void _simple_file_watcher_reinit(struct Simple_File_Watcher* watcher);
#endif

struct Simple_File_Watcher simple_file_watcher_init(const char* root_path, Fn_File_Filter *filter)
{
  struct Simple_File_Watcher watcher = {
    .filter = filter,
  };

#ifdef __linux__
  watcher.root_path = malloc(strlen(root_path)+1);
  watcher.watched_files = calloc(sizeof(*watcher.watched_files), 1);
  strcpy(watcher.root_path, root_path);

  watcher.dirs_fd = -1; // prevent _simple_file_watcher_reinit from closing the fd
  watcher.file_fd = -1; // prevent _simple_file_watcher_reinit from closing the fd
  _simple_file_watcher_reinit(&watcher);
  register_graceful_exit_via_sigint();
#endif // __linux__
  return watcher;
}

void simple_file_watcher_deinit(struct Simple_File_Watcher* watcher)
{
#ifdef __linux__
  free(watcher->root_path);
  free(watcher->watched_files);
  close(watcher->dirs_fd);
  close(watcher->file_fd);
#endif
}

#ifdef __linux__
bool _dir_to_ignore(const char* x)
{
  return x[0]=='.' && (x[1]==0 || (x[1]=='.' && x[2]==0) || (x[1]=='g' && x[2]=='i' && x[3]=='t' && x[4]==0));
}

// TODO: create dedicated path struct with helper funtions
#define PATH_BUFFER_CAPACITY 1024
usize path_join(char* path, const char* second, usize path_len)
{
  debug_assert_usize_lte(path_len+2, PATH_BUFFER_CAPACITY); // '/' and null terminator
  path[path_len++] = '/';

  usize second_len = strlen(second);
  debug_assert_usize_lt(path_len + second_len, PATH_BUFFER_CAPACITY);
  memcpy(path+path_len, second, second_len+1);
  return path_len+second_len;
}

static usize _simple_file_watcher_watch_subdirs(int dir_fd, struct Simple_File_Watcher* watcher, char* path, usize path_len)
{
  usize number_relevant_files_added = 0;

  u8 BUFFER[1024]
    __attribute((aligned(__alignof__(struct linux_dirent64))));

  ssize num;
  while((num = getdents64(dir_fd, BUFFER, sizeof(BUFFER))) != 0)
  {
    LINUX_ASSERT_NE(num, -1);

    for(ssize i=0; i<num;)
    {
      const struct linux_dirent64* entry = (const struct linux_dirent64*)&BUFFER[i];

      switch(entry->d_type)
      {
      case DT_DIR:
        if(!_dir_to_ignore(entry->d_name))
        {
          const usize new_len = path_join(path, entry->d_name, path_len); // modify path to point to the current dir
          // printf("dir: %s\n", path);

          const int subdir_wd = inotify_add_watch(watcher->dirs_fd, path, IN_MOVED_TO|IN_MOVE_SELF|IN_CREATE);
          LINUX_ASSERT_NE(subdir_wd, -1);

          const int subdir_fd = openat(dir_fd, entry->d_name, O_DIRECTORY | O_RDONLY, 0);
          LINUX_ASSERT_NE(subdir_fd, -1);
          number_relevant_files_added += _simple_file_watcher_watch_subdirs(subdir_fd, watcher, path, new_len);
          close(subdir_fd);

          path[path_len] = 0; // modify path to point to the parent dir, again
        }
        break;
      case DT_LNK:
      {
        // For now, symlinks to regular files aren't followed.
        // If I ever use symlinks to C files in my bootstrapper, this is the place to change.
        printf("warning: symlinks aren't followed for now(%s)\n", entry->d_name);
        break;
      }
      case DT_REG:
        if(watcher->filter(entry->d_name))
        {
          const usize new_len = path_join(path, entry->d_name, path_len); // modify path to point to the current dir
          // printf("regular file: %s\n", path);

          const int file_wd = inotify_add_watch(watcher->file_fd, path, IN_MODIFY|IN_DELETE_SELF|IN_MOVE_SELF);
          LINUX_ASSERT_NE(file_wd, -1);

          number_relevant_files_added += setintcddo_insert(watcher->watched_files, file_wd) == SETINTCDDOC_NEW;

          path[path_len] = 0; // modify path to point to the parent dir, again
        }
        break;
      }
      
      i += entry->d_reclen;
    }
  }

  return number_relevant_files_added;
}

static void _simple_file_watcher_rebuild_tree(struct Simple_File_Watcher* watcher);
static void _simple_file_watcher_reinit(struct Simple_File_Watcher* watcher)
{
  if(watcher->file_fd != -1)
    close(watcher->file_fd);

  // A dedicated inotify file descriptor for watching relevant files only
  watcher->file_fd = inotify_init1(IN_NONBLOCK);
  LINUX_ASSERT_NE(watcher->file_fd, -1);

  _simple_file_watcher_rebuild_tree(watcher);
}

static void _simple_file_watcher_rebuild_tree(struct Simple_File_Watcher* watcher)
{
  if(watcher->dirs_fd != -1)
    close(watcher->dirs_fd);

  // One inotify filedescriptor for watching directories (whether directories/files were added)
  watcher->dirs_fd = inotify_init1(IN_NONBLOCK);
  LINUX_ASSERT_NE(watcher->dirs_fd, -1);

  const int root_wd = inotify_add_watch(watcher->dirs_fd, watcher->root_path, IN_MOVED_TO|IN_MOVE_SELF|IN_CREATE);
  LINUX_ASSERT_NE(root_wd, -1);

  // recursively visit directories to watch them and their content, too
  {
    u8 PATH_BUFFER[PATH_BUFFER_CAPACITY];
    strcpy(PATH_BUFFER, realpath(watcher->root_path));
    
    const int root_dir_fd = open(watcher->root_path, O_DIRECTORY | O_RDONLY, 0);
    LINUX_ASSERT_NE(root_dir_fd, -1);
    _simple_file_watcher_watch_subdirs(root_dir_fd, watcher, PATH_BUFFER, strlen(PATH_BUFFER));
    close(root_dir_fd);
  }
}
#undef PATH_BUFFER_CAPACITY

static usize _simple_file_watcher_process_dir_events(struct Simple_File_Watcher* watcher)
{
  usize number_relevant_files_added = 0;

  u8 BUFFER[4096]
    __attribute((aligned(__alignof__(struct inotify_event))));

  bool rebuild_tree = false;
  bool reinit = false;
  while(true)
  {
    const ssize num_bytes_read = read(watcher->dirs_fd, BUFFER, sizeof(BUFFER));
    const bool nothing_mode_to_read = num_bytes_read == -1 && errno==EAGAIN;
    if(nothing_mode_to_read)
    {
      if(reinit)
        _simple_file_watcher_reinit(watcher);
      else if(rebuild_tree)
        _simple_file_watcher_rebuild_tree(watcher);
      return number_relevant_files_added;
    }
    
    for(ssize i=0; i<num_bytes_read;)
    {
      const struct inotify_event* event = (const struct inotify_event*)&BUFFER[i];

      switch(event->mask)
      {
      case IN_CREATE:
      case IN_MOVED_TO:
      case IN_MOVE_SELF:
        rebuild_tree = true;
        break;
      case IN_Q_OVERFLOW:
        reinit = true;
        break;
      }

      // TODO: write a helper printing inotify events
      // if(event->len != 0)
      // {
      //   printf("name: %s\n", event->name);
      // }else
      //   printf("\n");

      i += sizeof(struct inotify_event) + event->len;
    }
  }
}

void _simple_file_watcher_process_file_events(struct Simple_File_Watcher* watcher)
{
  u8 BUFFER[4096]
    __attribute((aligned(__alignof__(struct inotify_event))));
  while(true)
  {
    const ssize num_bytes_read = read(watcher->file_fd, BUFFER, sizeof(BUFFER));
    const bool nothing_mode_to_read = num_bytes_read == -1 && errno==EAGAIN;
    if(nothing_mode_to_read)
      return;
      
    for(ssize i=0; i<num_bytes_read;)
    {
      const struct inotify_event* event = (const struct inotify_event*)&BUFFER[i];

      // TODO print the event

      i += sizeof(struct inotify_event) + event->len;
    }
  }
}

bool simple_file_watcher_wait_for_change(struct Simple_File_Watcher* watcher)
{
  while(true)
  {
    usize relevant_files_changed = 0;
    {
      struct pollfd fds[2] = {
        (struct pollfd){
          .fd = watcher->dirs_fd,
          .events = POLLIN,
        },
        (struct pollfd){
          .fd = watcher->file_fd,
          .events = POLLIN,
        },
      };
      const nfds_t nfds = ARRAY_LEN(fds);

      const int result = poll(fds, nfds, -1);
      if(result==-1 && exit_requested)
      {
        printf(" done\n");
        return false;
      }
      LINUX_ASSERT_NE(result, -1);

      // If I would pass a `timeout`, I would need to check, whether any entry
      // had an event. Without a timeout, and errors already handeled we know
      // we had an event.
      debug_assert_int_gt(result, 0);

      // handle dir events
      if(fds[0].events & POLLIN)
      {
        usize number_relevant_files_added = _simple_file_watcher_process_dir_events(watcher);
        relevant_files_changed = number_relevant_files_added != 0;
      }

      // handle file events
      if(fds[1].events & POLLIN)
      {
        _simple_file_watcher_process_file_events(watcher);
        relevant_files_changed = true;
      }
    }

    if(relevant_files_changed)
      return true;
  }
}
#endif // __linux__

