// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "c_script.h"

#include "utils/x_macros.h"
#include "utils/collections/set/setintcddo.c"
#include "script/simple_file_watcher.c" // depends on setintcddo.c, x_macros.h

#define PRINT_ITER_STATS 1
#define CLEAR 1

enum C_Compiler
{
  CC_TCC,
  CC_GCC,
};
enum C_Compiler C_COMPILER = CC_TCC;

void run_tests()
{
#if CLEAR
  printf(TERM_CLEAR);
  fflush(stdout);
#endif

  // TODO: get the absolute path insteaed of depending on the current dir
  char test_path[] = "unit_test.c";
  char bin_path[] = "./unit_test";

  const u64 time_begin = timer_now();

  switch(C_COMPILER)
  {
  // TODO: allow choosing from more compilers.
  // If choosing libtcc, then simply fork and compile via the libtcc.
  case CC_TCC:
  {
    char* const args_compile[] = {"tcc", "-Wall", "-Werror", "-run", test_path, NULL};
    proc_exec_blocking(args_compile, (struct Proc_Exec_Blocking_Settings){});
    break;
  }
  case CC_GCC:
  {
    char* const args_compile[] = {"gcc", "-Wall", "-Werror", test_path, "-o", bin_path, NULL};
    char* const args_test[] = {bin_path, NULL};
    if(proc_exec_blocking(args_compile, (struct Proc_Exec_Blocking_Settings){}).exit_code == 0)
      proc_exec_blocking(args_test, (struct Proc_Exec_Blocking_Settings){});
    break;
  }
  }

  const u64 time_end = timer_now();

#if PRINT_ITER_STATS
  //TODO: fix memory leak!
  const char* duration = time_format_short_duration(time_end-time_begin, &SCRATCH);
  
  static usize iter_count = 0;
  // TODO print test iteration duration
  printf("%stest iteration: %zu duration: %s%s\n", TERM_CYAN, iter_count++, duration, TERM_NORMAL);
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
