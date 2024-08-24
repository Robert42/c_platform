// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "simple_file_watcher.h"
#include "gracefully_exit.c"

#ifdef __linux__
#include <sys/inotify.h>
#include <sys/poll.h>
#include <errno.h>
#endif

struct Simple_File_Watcher simple_file_watcher_init(const char* root_path, Fn_File_Filter *filter)
{
  struct Simple_File_Watcher watcher = {
    .filter = filter,
  };

#ifdef __linux__
  watcher.fd = inotify_init1(IN_NONBLOCK);
  LINUX_ASSERT_NE(watcher.fd, -1);

  const int root_wd = inotify_add_watch(watcher.fd, root_path, IN_MODIFY|IN_MOVE|IN_DELETE|IN_DELETE_SELF|IN_MOVE_SELF|IN_CREATE);
  LINUX_ASSERT_NE(root_wd, -1);

  // TODO: create watchers for each directory
#endif

  register_graceful_exit_via_sigint();
  return watcher;
}

bool simple_file_watcher_wait_for_change(struct Simple_File_Watcher* watcher)
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

  while(1)
  {
    __attribute((alignas(__alignof__(struct inotify_event))))
    u8 BUFFER[4096];

    const ssize num_bytes_read = read(watcher->fd, BUFFER, sizeof(BUFFER));
    if(num_bytes_read == -1 && errno==EAGAIN)
      return true;

    
    for(ssize i=0; i<num_bytes_read;)
    {
      const struct inotify_event* event = (const struct inotify_event*)&BUFFER[i];
      if(event->len != 0)
        printf("name: %s\n", event->name);
      i += sizeof(struct inotify_event) + event->len;
    }
  }
}
