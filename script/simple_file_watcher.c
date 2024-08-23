// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "simple_file_watcher.h"

struct Simple_File_Watcher simple_file_watcher_init(const char* root, Fn_File_Filter *filter)
{
  struct Simple_File_Watcher watcher = {
    .filter = filter,
#ifdef __linux__
    .watcher_fd = inotify_init(),
#endif
  };

#ifdef __linux__
  LINUX_ASSERT_NE(watcher.watcher_fd, -1);
  // TODO: create watchers for each directory
#endif

  return watcher;
}

bool simple_file_watcher_wait_for_change(struct Simple_File_Watcher* watcher)
{
  return false;
}
