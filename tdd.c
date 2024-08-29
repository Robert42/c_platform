// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "c_script.h"

#include "utils/x_macros.h"
#include "utils/collections/set/setintcddo.c"
#include "script/simple_file_watcher.c" // depends on setintcddo.c, x_macros.h

#include "c_compiler/c_static_analysis.c"

#define PRINT_ITER_STATS 1
#define CLEAR 1

enum Action
{
  ACTION_UNIT_TEST = 1,
  ACTION_STATIC_ANALYSIS = 2,
};

struct Config
{
  enum C_Compiler cc;
  u32 actions; // bit flag combination of `enum Action`

  enum C_Static_Analyzer static_analysis[C_STATIC_ANALYZER_COUNT];
  u32 num_static_analysis;
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
  printf(TERM_CLEAR);
  fflush(stdout);
#endif

  Path test_path = path_join(dir, path_from_cstr("unit_test.c"));
  Path bin_path = path_join(dir, path_from_cstr("unit_test"));

  const u64 time_begin = timer_now();
  if(cfg.actions & ACTION_STATIC_ANALYSIS)
    for(u32 i=0; i<cfg.num_static_analysis; ++i)
      c_static_analysis(cfg.static_analysis[i], test_path);
  if(cfg.actions & ACTION_UNIT_TEST)
    cc_compile_and_run(cfg.cc, test_path, bin_path);
  const u64 time_end = timer_now();

#if PRINT_ITER_STATS
  const char* duration = time_format_short_duration(time_end-time_begin, &SCRATCH);
  
  static usize iter_count = 0;
  printf("%stest iteration: %zu duration: %s%s\n", TERM_CYAN, iter_count++, duration, TERM_NORMAL);
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
    }else if(strcmp(argv[i], "--static_analysis") == 0)
    {
      if(++i >= argc) errx(EXIT_FAILURE, "Missing analyzer after `--static_analysis`\n");

      cfg.actions |= ACTION_STATIC_ANALYSIS;

      if(strcmp(argv[i], "all") == 0)
      {
        cfg.num_static_analysis = C_STATIC_ANALYZER_COUNT;
        for(u32 i=0; i<C_STATIC_ANALYZER_COUNT; ++i)
          cfg.static_analysis[i] = i;
      }else
      {
        const char* sep=",";
        char* tok = strtok(argv[i], sep);
        while(tok != NULL)
        {
          enum C_Static_Analyzer analyzer = c_static_analyzer_for_name(tok);
          for(u32 i=0; i<cfg.num_static_analysis; ++i)
            if(cfg.static_analysis[i] == analyzer) errx(EXIT_FAILURE, "Duplicate static_analyzer: `%s`", tok);
          debug_assert_usize_lt(cfg.num_static_analysis, C_STATIC_ANALYZER_COUNT); // no duplicates and the list is long enough to store all
          cfg.static_analysis[cfg.num_static_analysis++] = analyzer;
          tok = strtok(NULL, sep);
        }
      }
    }else if(strcmp(argv[i], "--unit_test") == 0)
      cfg.actions |= ACTION_UNIT_TEST;
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
