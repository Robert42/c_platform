// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "simple_file_watcher.h"

struct Simple_File_Watcher simple_file_watcher_init(const char* root, Fn_File_Filter *filter)
{
  struct Simple_File_Watcher watcher = {
    .filter = filter,
  };

  return watcher;
}

bool simple_file_watcher_wait_for_change(struct Simple_File_Watcher* watcher)
{
  return false;
}
