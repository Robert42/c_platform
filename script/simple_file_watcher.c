// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "simple_file_watcher.h"

#ifdef __linux__
#include "gracefully_exit.c"

#include <sys/inotify.h>
#include <sys/poll.h>
#include <errno.h>

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

  watcher.fd = -1; // prevent _simple_file_watcher_reinit from closing the fd
  _simple_file_watcher_reinit(&watcher);
  register_graceful_exit_via_sigint();
#endif // __linux__
  return watcher;
}

void simple_file_watcher_deinit(struct Simple_File_Watcher* watcher)
{
#ifdef __linux__
  free(watcher->root_path);
  close(watcher->fd);
#endif
}

#ifdef __linux__
static void _simple_file_watcher_reinit(struct Simple_File_Watcher* watcher)
{
  if(watcher->fd != -1)
    close(watcher->fd);

  watcher->fd = inotify_init1(IN_NONBLOCK);
  LINUX_ASSERT_NE(watcher->fd, -1);

  const int root_wd = inotify_add_watch(watcher->fd, watcher->root_path, IN_MODIFY|IN_MOVE|IN_DELETE|IN_DELETE_SELF|IN_MOVE_SELF|IN_CREATE);
  LINUX_ASSERT_NE(root_wd, -1);

  // TODO: create watchers for each directory
}

static bool _simple_file_watcher_process_events(struct Simple_File_Watcher* watcher)
{
  __attribute((alignas(__alignof__(struct inotify_event))))
  u8 BUFFER[4096];

  bool c_file_modified = false;
  while(true)
  {
    const ssize num_bytes_read = read(watcher->fd, BUFFER, sizeof(BUFFER));
    if(num_bytes_read == -1 && errno==EAGAIN)
      break;
    
    for(ssize i=0; i<num_bytes_read;)
    {
      const struct inotify_event* event = (const struct inotify_event*)&BUFFER[i];

      switch(event->mask)
      {
      case IN_CREATE:
        printf("IN_CREATE ", event->name);
        break;
      case IN_DELETE:
        printf("IN_DELETE ", event->name);
        break;
      case IN_DELETE_SELF:
        printf("IN_DELETE_SELF ", event->name);
        break;
      case IN_MODIFY:
        printf("IN_MODIFY ", event->name);
        break;
      case IN_MOVE_SELF:
        printf("IN_MOVE_SELF ", event->name);
        break;
      case IN_MOVED_FROM:
        printf("IN_MOVED_FROM ", event->name);
        break;
      case IN_MOVED_TO:
        printf("IN_MOVED_TO ", event->name);
        break;
      case IN_Q_OVERFLOW:
        printf("IN_Q_OVERFLOW ", event->name);
        // TODO: rebuild tree
        break;
      }
      if(event->len != 0)
      {
        printf("name: %s\n", event->name);
        c_file_modified = c_file_modified || watcher->filter(event->name);
      }else
        printf("\n", event->name);

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
          .fd = watcher->fd,
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

