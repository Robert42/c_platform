// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "simple_file_watcher.h"

#ifdef __linux__
#include <sys/inotify.h>
#endif

struct Simple_File_Watcher simple_file_watcher_init(const char* root_path, Fn_File_Filter *filter)
{
  struct Simple_File_Watcher watcher = {
    .filter = filter,
  };

#ifdef __linux__
  watcher.fd = inotify_init();
  LINUX_ASSERT_NE(watcher.fd, -1);

  const int root_wd = inotify_add_watch(watcher.fd, root_path, IN_MODIFY|IN_MOVE|IN_DELETE|IN_DELETE_SELF|IN_MOVE_SELF|IN_CREATE);
  LINUX_ASSERT_NE(root_wd, -1);

  // TODO: create watchers for each directory
#endif

  return watcher;
}

bool simple_file_watcher_wait_for_change(struct Simple_File_Watcher* watcher)
{
  u8 BUFFER[4096];
  ssize num_bytes_read = read(watcher->fd, BUFFER, sizeof(BUFFER));
  if(num_bytes_read != 0)
    return true;

  return false;
}
