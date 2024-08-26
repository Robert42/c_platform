// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "c_script.h"
#include "script/simple_file_watcher.c"

#define PRINT_ITER_STATS 1
#define CLEAR 1

void run_tests()
{
#if CLEAR
  printf(TERM_CLEAR);
  fflush(stdout);
#endif

  // TODO: get the absolute path insteaed of depending on the current dir
  char test_path[] = "unit_test.c";

  // TODO: allow choosing different compilers.
  // If choosing libtcc, then simply fork and compile via the libtcc.
  // char* const args[] = {"tcc", " -Wall", "-Werror", "-run", test_path};
  char* const args[] = {"tcc", "-Wall", "-Werror", "-run", test_path, NULL};
  struct Proc_Exec_Blocking_Result result = proc_exec_blocking(args, (struct Proc_Exec_Blocking_Settings){});

#if PRINT_ITER_STATS
  static usize iter_count = 0;
  // TODO print test iteration duration
  printf("%stest iteration: %zu%s\n", TERM_CYAN, iter_count++, TERM_NORMAL);
#endif
}

int main(int argc, const char** argv)
{
  c_script_init();

  run_tests();

  char path[] = __FILE__;
  struct Simple_File_Watcher watcher = simple_file_watcher_init(dirname(path), path_is_c_file);
  while(simple_file_watcher_wait_for_change(&watcher))
    run_tests();

  simple_file_watcher_deinit(&watcher);

  return 0;
}
