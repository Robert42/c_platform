// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "c_script.h"

#include "utils/x_macros.h"
#include "utils/collections/set/setintcddo.c"
#include "script/simple_file_watcher.c" // depends on setintcddo.c, x_macros.h

#define PRINT_ITER_STATS 1
#define CLEAR 1

void run_tests(enum C_Compiler cc)
{
#if CLEAR
  printf(TERM_CLEAR);
  fflush(stdout);
#endif

  // TODO: get the absolute path insteaed of depending on the current dir
  char test_path[] = "unit_test.c";
  char bin_path[] = "./unit_test";

  const u64 time_begin = timer_now();
  cc_compile_and_run(cc, test_path, bin_path);
  const u64 time_end = timer_now();

#if PRINT_ITER_STATS
  const char* duration = time_format_short_duration(time_end-time_begin, &SCRATCH);
  
  static usize iter_count = 0;
  printf("%stest iteration: %zu duration: %s%s\n", TERM_CYAN, iter_count++, duration, TERM_NORMAL);
#endif
}

int main(int argc, const char** argv)
{
  c_script_init();

  enum C_Compiler cc = CC_TCC;

  for(int i=1; i<argc; ++i)
  {
    if(strcmp(argv[i], "--cc") == 0)
    {
      if(++i >= argc) errx(EXIT_FAILURE, "Missing compiler after `--cc`\n");

      cc = cc_compiler_for_name(argv[i]);
    }
  }

  // Actual test loop
  run_tests(cc);

  char path[] = __FILE__;
  struct Simple_File_Watcher watcher = simple_file_watcher_init(dirname(path), path_is_c_file);
  while(simple_file_watcher_wait_for_change(&watcher))
  {
    run_tests(cc);
    scratch_swap();
  }

  simple_file_watcher_deinit(&watcher);

  return EXIT_SUCCESS;
}
