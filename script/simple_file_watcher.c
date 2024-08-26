// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "simple_file_watcher.h"

#ifdef __linux__
#include "gracefully_exit.c"

#include <sys/inotify.h>
#include <sys/poll.h>
#include <errno.h>
#include <fcntl.h>
#include <dirent.h>

#define DBG_EVENTS 0

static void _simple_file_watcher_reinit(struct Simple_File_Watcher* watcher);
#endif

struct Simple_File_Watcher simple_file_watcher_init(const char* root_path, Fn_File_Filter *filter)
{
  struct Simple_File_Watcher watcher = {
    .filter = filter,
  };

#ifdef __linux__
  watcher.root_path = realpath(root_path, NULL); // the result was allocated with malloc
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
          path_join(path, entry->d_name, path_len); // modify path to point to the current dir
          // printf("regular file: %s\n", path);

          const int file_wd = inotify_add_watch(watcher->file_fd, path, IN_MODIFY|IN_DELETE_SELF|IN_MOVE_SELF);
          LINUX_ASSERT_NE(file_wd, -1);

          const bool is_new = setintcddo_insert(watcher->watched_files, file_wd) == SETINTCDDOC_NEW;
          // if(is_new)
          //   printf("new relevant file found: %s\n", path);
          number_relevant_files_added += is_new;

          path[path_len] = 0; // modify path to point to the parent dir, again
        }
        break;
      }
      
      i += entry->d_reclen;
    }
  }

  return number_relevant_files_added;
}

static usize _simple_file_watcher_rebuild_tree(struct Simple_File_Watcher* watcher);
static void _simple_file_watcher_reinit(struct Simple_File_Watcher* watcher)
{
  if(watcher->file_fd != -1)
    close(watcher->file_fd);

  // A dedicated inotify file descriptor for watching relevant files only
  watcher->file_fd = inotify_init1(IN_NONBLOCK);
  LINUX_ASSERT_NE(watcher->file_fd, -1);

  _simple_file_watcher_rebuild_tree(watcher);
}

static usize _simple_file_watcher_rebuild_tree(struct Simple_File_Watcher* watcher)
{
  usize number_relevant_files_added = 0;
  if(watcher->dirs_fd != -1)
    close(watcher->dirs_fd);

  // One inotify filedescriptor for watching directories (whether directories/files were added)
  watcher->dirs_fd = inotify_init1(IN_NONBLOCK);
  LINUX_ASSERT_NE(watcher->dirs_fd, -1);

  const int root_wd = inotify_add_watch(watcher->dirs_fd, watcher->root_path, IN_MOVED_TO|IN_MOVE_SELF|IN_CREATE);
  LINUX_ASSERT_NE(root_wd, -1);

  // recursively visit directories to watch them and their content, too
  setintcddo_reset(watcher->watched_files);
  {
    char PATH_BUFFER[PATH_BUFFER_CAPACITY];
    strcpy(PATH_BUFFER, watcher->root_path);
    
    const int root_dir_fd = open(watcher->root_path, O_DIRECTORY | O_RDONLY, 0);
    LINUX_ASSERT_NE(root_dir_fd, -1);
    number_relevant_files_added = _simple_file_watcher_watch_subdirs(root_dir_fd, watcher, PATH_BUFFER, strlen(PATH_BUFFER));
    close(root_dir_fd);
  }
  number_relevant_files_added += watcher->watched_files->len_old != 0; // some relevant files were removed

  return number_relevant_files_added;
}
#undef PATH_BUFFER_CAPACITY

#if DBG_EVENTS
static const char* _inotify_event_mask_flag_to_cstr(u32 mask)
{
#define X_MACRO_INOTIFY_MASK(X) X(IN_ACCESS) X(IN_ATTRIB) X(IN_CLOSE_WRITE)\
  X(IN_CLOSE_NOWRITE) X(IN_CREATE) X(IN_DELETE) X(IN_DELETE_SELF) X(IN_MODIFY)\
  X(IN_MOVE_SELF) X(IN_MOVED_FROM) X(IN_MOVED_TO) X(IN_OPEN) X(IN_MOVE)\
  X(IN_CLOSE) X(IN_DONT_FOLLOW) X(IN_EXCL_UNLINK) X(IN_MASK_ADD) X(IN_ONESHOT)\
  X(IN_ONLYDIR) X(IN_MASK_CREATE) X(IN_IGNORED) X(IN_ISDIR) X(IN_Q_OVERFLOW)\
  X(IN_UNMOUNT)

  switch(mask)
  {
  X_MACRO_INOTIFY_MASK(X_CASE_RETURN_AS_CSTR)
  }
  return "?";
#undef X_MACRO_INOTIFY_MASK
}
static void _print_inotify_event(const struct inotify_event* event)
{
  printf("(struct inotify_event){\n  .wd = %i,\n  .mask = ", event->wd);

  u32 mask = event->mask;
  for(int i=0; mask!=0; ++i)
  {
    if(i!=0)
      printf("|");
    const u32 flag = mask & (mask ^ (mask-1));
    mask &= ~flag;
    printf("%s", _inotify_event_mask_flag_to_cstr(flag));
  }
  printf(",\n  .cookie = %u,\n  .name=`%s`\n}\n", event->cookie, event->len ? event->name : "");
}
#endif

#define RELEVANT_FILE_CHANGED 1
#define NEED_TO_REBUILD_TREE 2
#define NEED_TO_REINIT_EVERYTHING 4
typedef u32 _Simple_File_Watcher_Update;
static _Simple_File_Watcher_Update _simple_file_watcher_process_dir_events(struct Simple_File_Watcher* watcher)
{
  u8 BUFFER[4096]
    __attribute((aligned(__alignof__(struct inotify_event))));

  _Simple_File_Watcher_Update update = 0;
  while(true)
  {
    const ssize num_bytes_read = read(watcher->dirs_fd, BUFFER, sizeof(BUFFER));
    const bool nothing_mode_to_read = num_bytes_read == -1 && errno==EAGAIN;
    if(nothing_mode_to_read)
      return update;
    
    for(ssize i=0; i<num_bytes_read;)
    {
      const struct inotify_event* event = (const struct inotify_event*)&BUFFER[i];

#if DBG_EVENTS
      _print_inotify_event(event);
#endif

      if(event->mask & (IN_CREATE|IN_MOVED_TO|IN_MOVE_SELF))
        update |= NEED_TO_REBUILD_TREE;
      if(event->mask & IN_Q_OVERFLOW)
        update |= NEED_TO_REINIT_EVERYTHING;

      i += sizeof(struct inotify_event) + event->len;
    }
  }
}

_Simple_File_Watcher_Update _simple_file_watcher_process_file_events(struct Simple_File_Watcher* watcher)
{
  u8 BUFFER[4096]
    __attribute((aligned(__alignof__(struct inotify_event))));
  _Simple_File_Watcher_Update update = 0;
  while(true)
  {
    const ssize num_bytes_read = read(watcher->file_fd, BUFFER, sizeof(BUFFER));
    const bool nothing_mode_to_read = num_bytes_read == -1 && errno==EAGAIN;
    if(nothing_mode_to_read)
      return update;
      
    for(ssize i=0; i<num_bytes_read;)
    {
      const struct inotify_event* event = (const struct inotify_event*)&BUFFER[i];

#if DBG_EVENTS
      _print_inotify_event(event);
#endif
      if(event->mask & (IN_MODIFY|IN_DELETE_SELF|IN_MOVE_SELF))
        update |= RELEVANT_FILE_CHANGED;
      if(event->mask & IN_DELETE_SELF)
      {
        setintcddo_remove(watcher->watched_files, event->wd);
        update |= RELEVANT_FILE_CHANGED;
      }
      if(event->mask & IN_MOVE_SELF)
      {
        setintcddo_remove(watcher->watched_files, event->wd);
        update |= NEED_TO_REBUILD_TREE;
      }

      i += sizeof(struct inotify_event) + event->len;
    }
  }
}

bool simple_file_watcher_wait_for_change(struct Simple_File_Watcher* watcher)
{
  while(true)
  {
    _Simple_File_Watcher_Update update = 0;
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
        update |= _simple_file_watcher_process_dir_events(watcher);

      // handle file events
      if(fds[1].events & POLLIN)
        update |= _simple_file_watcher_process_file_events(watcher);
    }

    if(update & NEED_TO_REINIT_EVERYTHING)
    {
      _simple_file_watcher_reinit(watcher);
      return true;
    }
    else if(update & NEED_TO_REBUILD_TREE)
    {
      const usize num_relevant_files_changed = _simple_file_watcher_rebuild_tree(watcher);
      if(num_relevant_files_changed != 0)
        update |= RELEVANT_FILE_CHANGED;
    }

    if(update & RELEVANT_FILE_CHANGED)
      return true;
  }
}

#undef RELEVANT_FILE_CHANGED
#undef NEED_TO_REBUILD_TREE
#undef NEED_TO_REINIT_EVERYTHING

#undef DBG_EVENTS
#endif // __linux__

