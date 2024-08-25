// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "c_script.h"
#include "script/simple_file_watcher.c"

#include "platform/test.c"
#include "utils/test.c"

int main(int argc, const char** argv)
{
  c_script_init();

  term_demo();
  dev_env_demo();

  platform_test();
  utils_test();

  printf("%s==== DONE ====%s\n", TERM_GREEN_BOLD, TERM_NORMAL);

  char path[] = __FILE__;
  struct Simple_File_Watcher watcher = simple_file_watcher_init(dirname(path), path_is_c_file);
  while(simple_file_watcher_wait_for_change(&watcher))
  {
    printf("C FILE CHANGED!\n");
  }

  simple_file_watcher_deinit(&watcher);

  return 0;
}
