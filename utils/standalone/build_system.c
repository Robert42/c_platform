// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "../../c_script.h"
#include "../collections/set/setintcddo.c"
#include "../script/simple_file_watcher.c" // depends on setintcddo.c, x_macros.h

#define PRINT_ITER_STATS 1
#define CLEAR 1
#define PRINT_PATHS_AND_EXIT 0

struct Unit_Test
{
  const char* src;
};

struct Build_System_Data
{
  struct Unit_Test unit_test[1024];
  usize unit_test_count;
};

enum Action
{
  ACTION_UNIT_TEST = 1<<0,
};

struct Config
{
  enum C_Compiler cc;
  u32 actions; // bit flag combination of `enum Action`
  Path build_ini_path;
};

static struct Config cfg_default()
{
  return (struct Config){
    .cc = cc_fastest_available(),
    .build_ini_path = path_from_cstr("build.ini"),
  };
}

static struct Config build_system_cfg_load(int argc, const char** argv);
static struct Build_System_Data build_system_ini_load(Path ini_file);

static void run_unit_test(struct Config cfg, Path bin_path, Path c_path);

int main(int argc, const char** argv)
{
  c_script_init();

  struct Config cfg = build_system_cfg_load(argc, argv);
  const Path build_path = path_parent(cfg.build_ini_path);

#if PRINT_PATHS_AND_EXIT
  printf("cfg.build_ini_path: <%s>\n", cfg.build_ini_path.cstr);
  printf("build_path: <%s>\n", build_path.cstr);
  return 0;
#endif
  struct Build_System_Data data = build_system_ini_load(cfg.build_ini_path);

  const Path unit_test_bin_file = path_join(build_path, path_from_cstr("unit_test.exe"));

  struct Simple_File_Watcher watcher = simple_file_watcher_init(build_path, path_is_c_file);
  do
  {
#if CLEAR
    printf("%s", TERM.clear);
    fflush(stdout);
#endif

    const u64 time_begin = timer_now();
    if(cfg.actions & ACTION_UNIT_TEST)
    {
      switch(data.unit_test_count)
      {
      case 0:
        PANIC("No uni_test to run");
      case 1:
        run_unit_test(cfg, unit_test_bin_file, path_join(build_path, path_from_cstr(data.unit_test[0].src)));
        break;
      default:
        UNIMPLEMENTED("Don't know which unit_test to choose");
      }
    }
    const u64 time_end = timer_now();

#if PRINT_ITER_STATS
    const char* duration = time_format_short_duration(time_end-time_begin, &SCRATCH);

    static usize iter_count = 0;
    printf("%siteration: %zu duration: %s%s\n", TERM.cyan, iter_count++, duration, TERM.normal);
#endif
    scratch_swap();
  } while(simple_file_watcher_wait_for_change(&watcher));
}

static struct Ini_Format build_system_format(struct Build_System_Data* data)
{
  struct Ini_Format ini_format = {};

  {
    INI_FORMAT_SECTION_BEGIN(struct Unit_Test, unit_test, data->unit_test, ARRAY_LEN(data->unit_test), &data->unit_test_count);
    INI_FORMAT_FIELD(src);
    INI_FORMAT_SECTION_END();
  }

  return ini_format;
}

static struct Config build_system_cfg_load(int argc, const char** argv)
{
  struct Config cfg = cfg_default();

  for(int i=1; i<argc; ++i)
  {
    if(strcmp(argv[i], "--cc") == 0)
    {
      if(++i >= argc) errx(EXIT_FAILURE, "Missing compiler after `--cc`\n");

      cfg.cc = cc_compiler_for_name(argv[i]);
    }else if(strcmp(argv[i], "--unit_test") == 0)
      cfg.actions |= ACTION_UNIT_TEST;
    else if(i+1 == argc)
      cfg.build_ini_path = path_from_cstr(argv[i]);
  }

  if(cfg.actions == 0)
    cfg.actions = ACTION_UNIT_TEST;

  return cfg;
}

static struct Build_System_Data build_system_ini_load(Path ini_file)
{
  struct Build_System_Data data = {};
  struct Ini_Format ini_format = build_system_format(&data);
  {
    const Mem_Region _prev = STACK;
    const char* text = file_text_read_to_cstr(ini_file, &STACK);
    ini_parse(&SCRATCH, &ini_format, text);
    STACK = _prev;
  }

  return data;
}

static void run_unit_test(struct Config cfg, Path bin_path, Path c_path)
{
  cc_compile_and_run(cfg.cc, c_path, bin_path);
  // TODO: ONLY if the process succeeded!
  printf("%s==== unit_test: DONE ====%s\n", TERM.green_bold, TERM.normal);
}

