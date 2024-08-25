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
  strcpy(watcher.root_path, root_path);

  watcher.dirs_fd = -1; // prevent _simple_file_watcher_reinit from closing the fd
  _simple_file_watcher_reinit(&watcher);
  register_graceful_exit_via_sigint();
#endif // __linux__
  return watcher;
}

void simple_file_watcher_deinit(struct Simple_File_Watcher* watcher)
{
#ifdef __linux__
  free(watcher->root_path);
  close(watcher->dirs_fd);
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

static void _simple_file_watcher_watch_subdirs(int dir_fd, struct Simple_File_Watcher* watcher, char* path, usize path_len)
{
  u8 BUFFER[1024]
    __attribute((aligned(__alignof__(struct linux_dirent64))));

  ssize num;
  while((num = getdents64(dir_fd, BUFFER, sizeof(BUFFER))) != 0)
  {
    LINUX_ASSERT_NE(num, -1);

    for(ssize i=0; i<num;)
    {
      const struct linux_dirent64* entry = (const struct linux_dirent64*)&BUFFER[i];

      if(entry->d_type == DT_DIR && !_dir_to_ignore(entry->d_name))
      {
        const usize new_len = path_join(path, entry->d_name, path_len); // modify path to point to the current dir
        // printf("dir: %s\n", path);

        const int subdir_wd = inotify_add_watch(watcher->dirs_fd, path, IN_MODIFY|IN_MOVE|IN_DELETE|IN_DELETE_SELF|IN_MOVE_SELF|IN_CREATE);
        LINUX_ASSERT_NE(subdir_wd, -1);

        const int subdir_fd = openat(dir_fd, entry->d_name, O_DIRECTORY | O_RDONLY, 0);
        LINUX_ASSERT_NE(subdir_fd, -1);
        _simple_file_watcher_watch_subdirs(subdir_fd, watcher, path, new_len);
        close(subdir_fd);

        path[path_len] = 0;
      }
      
      i += entry->d_reclen;
    }
  }
}

static void _simple_file_watcher_reinit(struct Simple_File_Watcher* watcher)
{
  if(watcher->dirs_fd != -1)
    close(watcher->dirs_fd);

  watcher->dirs_fd = inotify_init1(IN_NONBLOCK);
  LINUX_ASSERT_NE(watcher->dirs_fd, -1);

  const int root_wd = inotify_add_watch(watcher->dirs_fd, watcher->root_path, IN_MODIFY|IN_MOVE|IN_DELETE|IN_DELETE_SELF|IN_MOVE_SELF|IN_CREATE);
  LINUX_ASSERT_NE(root_wd, -1);

  // recursively visit directories to watch those, too
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

static bool _simple_file_watcher_process_events(struct Simple_File_Watcher* watcher)
{
  u8 BUFFER[4096]
    __attribute((aligned(__alignof__(struct inotify_event))));

  bool c_file_modified = false;
  while(true)
  {
    const ssize num_bytes_read = read(watcher->dirs_fd, BUFFER, sizeof(BUFFER));
    const bool nothing_mode_to_read = num_bytes_read == -1 && errno==EAGAIN;
    if(nothing_mode_to_read)
      break;
    
    for(ssize i=0; i<num_bytes_read;)
    {
      const struct inotify_event* event = (const struct inotify_event*)&BUFFER[i];

      switch(event->mask)
      {
      case IN_CREATE:
        printf("IN_CREATE ");
        break;
      case IN_DELETE:
        printf("IN_DELETE ");
        break;
      case IN_DELETE_SELF:
        printf("IN_DELETE_SELF ");
        break;
      case IN_MODIFY:
        printf("IN_MODIFY ");
        break;
      case IN_MOVE_SELF:
        printf("IN_MOVE_SELF ");
        break;
      case IN_MOVED_FROM:
        printf("IN_MOVED_FROM ");
        break;
      case IN_MOVED_TO:
        printf("IN_MOVED_TO ");
        break;
      case IN_Q_OVERFLOW:
        printf("IN_Q_OVERFLOW ");
        // TODO: rebuild tree
        break;
      }
      if(event->len != 0)
      {
        printf("name: %s\n", event->name);
        c_file_modified = c_file_modified || watcher->filter(event->name);
      }else
        printf("\n");

      i += sizeof(struct inotify_event) + event->len;
    }
  }

  return c_file_modified;
}

bool simple_file_watcher_wait_for_change(struct Simple_File_Watcher* watcher)
{
  while(true)
  {
    {
      struct pollfd fds[1] = {
        (struct pollfd){
          .fd = watcher->dirs_fd,
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

      // If I had either had multiple `struct pollfd` entries in `fds` or pass a
      // `timeout`, I would need to check, whether/which entry had an event.
      // Without any of these, and errors already handeled we know we had an
      // event.
      debug_assert_int_eq(result, 1);
      debug_assert_bool_eq(fds[0].events & POLLIN, true);
    }

    if(_simple_file_watcher_process_events(watcher))
      return true;
  }
}
#endif // __linux__

