// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "c_script.h"

#include "utils/collections/set/setintcddo.c"
#include "script/simple_file_watcher.c" // depends on setintcddo.c, x_macros.h

#define PRINT_ITER_STATS 1
#define CLEAR 1

enum Action
{
  ACTION_UNIT_TEST = 1<<0,
  ACTION_VERIFY = 1<<1,
  ACTION_ALL_TESTS = 1<<2,
  ACTION_CODEGEN = 1<<3,
};

struct Config
{
  enum C_Compiler cc;
  u32 actions; // bit flag combination of `enum Action`
};

struct Config cfg_default()
{
  return (struct Config){
    .cc = cc_fastest_available(),
  };
}

void run_tests(struct Config cfg, Path dir)
{
#if CLEAR
  printf("%s", TERM.clear);
  fflush(stdout);
#endif

  const u64 time_begin = timer_now();
  if(cfg.actions & ACTION_ALL_TESTS)
  {
    Path bin_path = path_join(dir, path_from_cstr("all_tests"));
    Path test_path = path_append_cstr(bin_path, ".c");
    cc_compile_and_run(cfg.cc, test_path, bin_path);
  }
  if(cfg.actions & ACTION_UNIT_TEST)
  {
    Path bin_path = path_join(dir, path_from_cstr("unit_test"));
    Path test_path = path_append_cstr(bin_path, ".c");
    cc_compile_and_run(cfg.cc, test_path, bin_path);
  }
  if(cfg.actions & ACTION_VERIFY)
  {
    Path bin_path = path_join(dir, path_from_cstr("verify"));
    Path test_path = path_append_cstr(bin_path, ".c");
    cc_compile_and_run(cfg.cc, test_path, bin_path);
  }
  if(cfg.actions & ACTION_CODEGEN)
  {
    Path bin_path = path_join(dir, path_from_cstr("codegen"));
    Path test_path = path_append_cstr(bin_path, ".c");
    cc_compile_and_run(cfg.cc, test_path, bin_path);
  }
  const u64 time_end = timer_now();

#if PRINT_ITER_STATS
  const char* duration = time_format_short_duration(time_end-time_begin, &SCRATCH);
  
  static usize iter_count = 0;
  printf("%stest iteration: %zu duration: %s%s\n", TERM.cyan, iter_count++, duration, TERM.normal);
#endif
}

int main(int argc, char** argv)
{
  c_script_init();
  const Path dir = path_parent(path_realpath(path_from_cstr(__FILE__)));

  struct Config cfg = cfg_default();

  for(int i=1; i<argc; ++i)
  {
    if(strcmp(argv[i], "--cc") == 0)
    {
      if(++i >= argc) errx(EXIT_FAILURE, "Missing compiler after `--cc`\n");

      cfg.cc = cc_compiler_for_name(argv[i]);
    }else if(strcmp(argv[i], "--unit_test") == 0)
      cfg.actions |= ACTION_UNIT_TEST;
    else if(strcmp(argv[i], "--verify") == 0)
      cfg.actions |= ACTION_VERIFY;
    else if(strcmp(argv[i], "--all_tests") == 0)
      cfg.actions |= ACTION_ALL_TESTS;
    else if(strcmp(argv[i], "--codegen") == 0)
      cfg.actions |= ACTION_CODEGEN;
    else
      errx(EXIT_FAILURE, "Unexpected argument `%s`\n", argv[i]);
  }

  if(cfg.actions == 0)
    cfg.actions = ACTION_UNIT_TEST;

  // Actual test loop
  run_tests(cfg, dir);

  struct Simple_File_Watcher watcher = simple_file_watcher_init(dir, path_is_c_file);
  while(simple_file_watcher_wait_for_change(&watcher))
  {
    run_tests(cfg, dir);
    scratch_swap();
  }

  simple_file_watcher_deinit(&watcher);

  return EXIT_SUCCESS;
}
