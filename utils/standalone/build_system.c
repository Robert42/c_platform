// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "../../c_script.h"
#include "../collections/set/setintcddo.c"
#include "../script/simple_file_watcher.c" // depends on setintcddo.c, x_macros.h
#include "build_system/project.h"

// ```
// clear && gcc -O2 utils/standalone/build_system.c -o utils/standalone/bs && utils/standalone/bs /path/to/build.ini
// ```

#define PRINT_ITER_STATS 1
#define CLEAR 1
#define PRINT_PATHS_AND_EXIT 0

struct Config
{
  const char* action_name;
  enum C_Compiler cc;
  usize action; // index
  Path build_ini_path;
  bool verbose;
  bool debug_build;
  bool static_analysis;
  bool sanitize_memory;
  bool once;
  bool clear;
  bool full_check;
};

struct Context
{
  struct Config* cfg;
  struct Project* project;
};

static struct Config cfg_default()
{
  return (struct Config){
    .cc = cc_fastest_available(),
    .action = USIZE_MAX,
    .build_ini_path = path_from_cstr("build.ini"),
    .verbose = false,
    .debug_build = false,
    .static_analysis = false,
    .sanitize_memory = false,
    .once = false,
    .clear = true,
    .action_name = NULL,
  };
}

static struct Config build_system_cfg_load(int argc, const char** argv);
static bool watch_files_filter(const char* filepath, const struct Context* ctx);

static struct Project project_load(struct Config* cfg);
static int full_check(struct Config cfg, struct Project project);

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
  struct Project project = project_load(&cfg);
  if(project.action_count == 0)
    return 0;

  if(cfg.full_check)
    return full_check(cfg, project);

  if(cfg.action_name != NULL)
  {
    for(usize i=0; i<project.action_count; ++i)
      if(cstr_eq(project.action[i].name, cfg.action_name))
      {
        cfg.action = i;
        break;
      }
    if(cfg.action == USIZE_MAX)
    {
      fprintf(stderr, "Unknown action `%s`\n", cfg.action_name);
      return EXIT_FAILURE;
    }
  }

  struct Context ctx = {
    .cfg = &cfg,
    .project = &project,
  };
  struct Simple_File_Watcher watcher;
  usize prev_action = USIZE_MAX;
  do
  {
    while(cfg.action == USIZE_MAX)
    {
#if CLEAR
      printf("%s", TERM.clear);
      fflush(stdout);
#endif

      printf("Available actions:\n");
      for(usize i=0; i<project.action_count; ++i)
        printf("- %s\n", project.action[i].name);

      char buf[4096];
      char* choice = buf;
      printf("Choose action: ");
      fgets(choice, sizeof(buf), stdin);
      if(feof(stdin))
        return 0;

      printf("Choice: %s\n", choice);

      usize len = strlen(choice);
      if(len > 0 && choice[len-1]=='\n')
      {
        choice[len-1] = 0;
        len--;
      }
      
      usize num_matches = 0;
      usize match_so_far;
      for(usize i=0; i<project.action_count; ++i)
        if(cstr_starts_with(project.action[i].name, choice))
        {
          switch(num_matches)
          {
          case 0:
            match_so_far = i;
            break;
          case 1:
            printf("Multiple matching candidates:\n");
            printf("- %s\n", project.action[match_so_far].name);
            printf("- %s\n", project.action[i].name);
            break;
          default:
            printf("- %s\n", project.action[i].name);
            break;
          }
          num_matches++;
        }
      if(num_matches == 1)
        cfg.action = match_so_far;
    }

    // If another action was chosen, switch which files to watch
    if(prev_action != cfg.action)
    {
      if(prev_action != USIZE_MAX)
        simple_file_watcher_deinit(&watcher);
      prev_action = cfg.action;

      const Path* paths_to_watch = project.action[cfg.action].trigger_fs_path;
      usize paths_to_watch_count = project.action[cfg.action].trigger_fs_path_count;
      if(paths_to_watch_count == 0)
      {
        paths_to_watch = &build_path;
        paths_to_watch_count = 1;
      }
      watcher = simple_file_watcher_init(paths_to_watch, paths_to_watch_count, (Fn_File_Filter*)&watch_files_filter, &ctx);
    }

#if CLEAR
    if(cfg.clear)
    {
      printf("%s", TERM.clear);
      fflush(stdout);
    }
#endif
#if PRINT_ITER_STATS
    u64 duration = UINT64_MAX;
#endif

    const struct Project_Action action = project.action[cfg.action];

    switch(action.variant)
    {
    case ACTION_NONE:
      printf("%s==== %s: NOP ====%s\n", TERM.green, action.name, TERM.normal);
      if(cfg.once)
        return EXIT_SUCCESS;
      break;
    case ACTION_CC:
    {
      const struct C_Compiler_Config cc = action.cc;
      if(cfg.verbose)
        cc_command_print(cc);
      const u64 time_begin = timer_now();
      const struct CC_Status status = cc_run(cc);
      const u64 time_end = timer_now();
      duration = time_end - time_begin;

      const char* what = cc_status_attempted_name(status);
      const char* result = cc_status_is_success(status) ? "SUCCESS" : "FAILURE";
      const char* color = cc_status_is_success(status) ? TERM.green : TERM.red;
      const char* color_bold = cc_status_is_success(status) ? TERM.green_bold : TERM.red_bold;
      printf("%s==== %s%s%s: %s%s%s (%s) ====%s\n", color, color_bold, action.name, color, color_bold, result, color, what, TERM.normal);
      if(cfg.once)
        return cc_status_is_success(status) ? EXIT_SUCCESS : EXIT_FAILURE;
      break;
    }
    }

#if PRINT_ITER_STATS
    const char* duration_cstr = duration!=UINT64_MAX ? time_format_short_duration(duration, &SCRATCH) : "---";

    static usize iter_count = 0;
    printf("%siteration: %zu duration: %s%s\n", TERM.cyan, iter_count++, duration_cstr, TERM.normal);
#else
    (void)duration;
#endif
    scratch_swap();
  } while(simple_file_watcher_wait_for_change(&watcher));
}

bool _full_check_run(struct Project_Action action, struct Config cfg, struct C_Compiler_Config cc)
{
  const char* doing;
  if(cc.static_analysis)
    doing = "analyze";
  else if(cc.sanitize_memory)
    doing = "sanitize";
  else
    doing = "compile & run";

  if(TERM.clear_line[0])
  {
    printf("%s (%s) ...", doing, cc_compiler_name(cc.cc));
    fflush(stdout);
  }

  if(cfg.verbose)
  {
    puts("\nCommand:\n```");
    cc_command_print(cc);
    puts("```\n");
  }
  const u64 time_begin = timer_now();
  const bool succeeded = cc_status_is_success(cc_run(cc));
  const u64 time_end = timer_now();
  const u64 duration = time_end - time_begin;

  const char* duration_cstr = duration!=UINT64_MAX ? time_format_short_duration(duration, &SCRATCH) : "---";

  const char* style_name = succeeded ? TERM.green : TERM.red;
  const char* style_result = succeeded ? TERM.green_bold : TERM.red_bold;
  const char* result = succeeded ? "SUCCESS" : "FAILURE";

  printf("%s%s%s (%s) %s%s %s(%s)%s\n", TERM.clear_line, style_name, doing, cc_compiler_name(cc.cc), style_result, result, style_name, duration_cstr, TERM.normal);
  fflush(stdout);

  return succeeded;
}

static int full_check(struct Config cfg, struct Project project)
{
  bool any_compiler_found = false;

  for(usize i_action=0; i_action<project.action_count; ++i_action)
  {
    const struct Project_Action action = project.action[i_action];
    const struct C_Compiler_Config action_cc = action.cc;

    printf("==== %s ====\n", action.name);

    for(usize i_compiler=0; i_compiler<CC_COUNT; ++i_compiler)
    {
      const enum C_Compiler cc = (enum C_Compiler)i_compiler;
      if(!cc_compiler_is_available(cc))
        continue;
      any_compiler_found = true;

      if(cc == CC_TCC || 
        action_cc.sanitize_memory ||
        action_cc.static_analysis)
      {
        if(!_full_check_run(action, cfg, action_cc))
          return EXIT_FAILURE;
        continue;
      }

      if(cc != CC_GCC)
      {
        struct C_Compiler_Config cc_cfg = action_cc;
        cc_cfg.static_analysis = true;
        cc_cfg.cc = cc;
        if(!_full_check_run(action, cfg, cc_cfg))
          return EXIT_FAILURE;
      }

      {
        struct C_Compiler_Config cc_cfg = action_cc;
        cc_cfg.sanitize_memory = true;
        cc_cfg.cc = cc;
        if(!_full_check_run(action, cfg, cc_cfg))
          return EXIT_FAILURE;
      }
    }
  }

  if(!any_compiler_found)
  {
    fprintf(stderr, "No supported C compiler found!\n");
    return EXIT_FAILURE;
  }

  return EXIT_SUCCESS;
}

static struct Config build_system_cfg_load(int argc, const char** argv)
{
  struct Config cfg = cfg_default();

  bool explicit_cc = false;
  for(int i=1; i<argc; ++i)
  {
    if(strcmp(argv[i], "--cc") == 0)
    {
      if(++i >= argc) errx(EXIT_FAILURE, "Missing compiler after `--cc`\n");

      cfg.cc = cc_compiler_for_name(argv[i]);
      explicit_cc = true;
    }else if(cstr_eq(argv[i], "-v"))
    {
      cfg.verbose = true;
    }else if(cstr_eq(argv[i], "-g"))
    {
      cfg.debug_build = true;
    }else if(cstr_eq(argv[i], "--once"))
    {
      cfg.once = true;
      if(++i >= argc) errx(EXIT_FAILURE, "Missing action after `--once`\n");

      cfg.action_name = argv[i];
    }else if(cstr_eq(argv[i], "--sanitize"))
    {
      cfg.sanitize_memory = true;
    }else if(cstr_eq(argv[i], "--analyze"))
    {
      cfg.static_analysis = true;
    }else if(cstr_eq(argv[i], "--no_clear"))
    {
      cfg.clear = false;
    }else if(cstr_eq(argv[i], "--full_check"))
    {
      cfg.full_check = true;
    }else if(i+1 == argc && argv[i][0]!='-')
      cfg.build_ini_path = path_from_cstr(argv[i]);
    else
      errx(EXIT_FAILURE, "Unexpected argument\n```\n%s\n```\n", argv[i]);
  }

  if(cfg.cc == CC_TCC && (
    cfg.sanitize_memory
    || cfg.static_analysis
    ))
  {
    if(explicit_cc)
      errx(EXIT_FAILURE, "tcc does not support sanitizers nor static analysis\n");
    cfg.cc = CC_CLANG;
  }
    

  cfg.build_ini_path = path_realpath(cfg.build_ini_path);

  if(cfg.static_analysis)
  {
    switch(cfg.cc)
    {
    case CC_CLANG: 
      break; // All fine, nothing to change
    case CC_GCC: // The gcc version I have installed is not able to analyze the whole project
    case CC_TCC: // tcc has no static analysis at all.
      cfg.cc = CC_CLANG;
      break;
    }
  }

  return cfg;
}

static bool watch_files_filter(const char* filepath, const struct Context* ctx)
{
  const struct Project_Action* action = &ctx->project->action[ctx->cfg->action];
  return path_has_suffix_one_of(filepath, action->trigger_fs_suffix, action->trigger_fs_suffix_count);
}

static struct Project project_load(struct Config* cfg)
{
  const Path dir = path_parent(cfg->build_ini_path);
  struct Project project = {};

  struct Build_Ini_Root root = {};
  {
    struct Ini_Format ini_format = build_ini_format(&root);
    const Mem_Region _prev = STACK;
    const char* text = file_text_read_to_cstr(cfg->build_ini_path, &STACK);
    ini_parse(&PERSISTENT, &ini_format, text);
    STACK = _prev;
  }

  project.action_count = root.action_count;
  for(usize i_action=0; i_action<root.action_count; ++i_action)
  {
    struct Project_Action* action = &project.action[i_action];
    const struct Build_Ini_Action* ini_action = &root.action[i_action];

    action->name = ini_action->name;

    const usize watch_path_count = ini_action->trigger_fs_path_count;
    Path* watch_paths = MEM_REGION_ALLOC_ARRAY(&PERSISTENT, Path, watch_path_count);
    for(usize i_path=0; i_path<watch_path_count; ++i_path)
      watch_paths[i_path] = path_join(dir, path_from_cstr(ini_action->trigger_fs_path[i_path]));
    action->trigger_fs_path_count = watch_path_count;
    action->trigger_fs_path = watch_paths;

    action->trigger_fs_suffix_count = ini_action->trigger_fs_suffix_count;
    action->trigger_fs_suffix = ini_action->trigger_fs_suffix;

    for(usize i_suffix=0; i_suffix<action->trigger_fs_suffix_count; ++i_suffix)
    {
      const char* suffix = action->trigger_fs_suffix[i_suffix];
      if(suffix[0] != '*')
        PANIC("suffix `%s` not support.\nRequirement: Starts with `*`");
      if(strchr(suffix+1, '*') != NULL)
        PANIC("suffix `%s` not support.\nRequirement: Contains exactly one `*`");
      if(strchr(suffix, '?') != NULL)
        PANIC("suffix `%s` not support.\nRequirement: Contains no `?`");

      if(cfg->verbose)
        printf("suffix: `%s`\n", suffix);
      action->trigger_fs_suffix[i_suffix] = suffix+1; // skip the leading `*`
    }

    if(ini_action->cmd_count==0)
      action->variant = ACTION_NONE;
    else if(cstr_eq(ini_action->cmd[0], "cc"))
    {
      action->variant = ACTION_CC;
      struct C_Compiler_Config cc = {
        .cc = cfg->cc,
        .c_version = C_VERSION_2011,
        .debug = cfg->debug_build,
        .disable_vla = true, // TODO
        .sanitize_memory = cfg->sanitize_memory,
        .static_analysis = cfg->static_analysis,
        .c_file = {},
        .skip_warning_flags = false,
        .gen_parent_dir = true,
        .capture_run_stdout = false,
      };

      for(usize i_cmd = 1; i_cmd<ini_action->cmd_count; ++i_cmd)
      {
        const char* cmd = ini_action->cmd[i_cmd];
        if(cstr_starts_with(cmd, "-std="))
        {
          cmd += 5;
          cc.c_version = cc_version_for_name(cmd);
        }
        else if(cstr_starts_with(cmd, "-I"))
        {
          cmd += 2;

          Path* include_dir = MEM_REGION_ALLOC(&PERSISTENT, Path);
          *include_dir = path_join(dir, path_from_cstr(cmd));

          assert_usize_lt(cc.include_dir_count, ARRAY_LEN(cc.include_dir));
          cc.include_dir[cc.include_dir_count++] = include_dir;
        }
        else if(cstr_ends_with(cmd, ".c"))
          cc.c_file = path_join(dir, path_from_cstr(cmd));
        else if(cstr_eq(cmd, "-g"))
          cc.debug = true;
        else if(cstr_eq(cmd, "--analyze"))
          cc.static_analysis = true;
        else if(cstr_eq(cmd, "-o"))
        {
          i_cmd++;
          if(i_cmd == ini_action->cmd_count)
            PANIC("Expect argument after `-o`");
          cc.output_file = path_join(dir, path_from_cstr(ini_action->cmd[i_cmd]));
        }
        else if(cstr_eq(cmd, "&&"))
        {
          i_cmd++;
          if(i_cmd == ini_action->cmd_count)
            PANIC("Expect command after `&&`");
          if(!cstr_eq(cc.output_file.cstr, path_join(dir, path_from_cstr(ini_action->cmd[i_cmd])).cstr))
            PANIC("Executing anything but the output after `&&` is not implemented");
          i_cmd++;

          cc.run_args = &ini_action->cmd[i_cmd];
          for(; i_cmd<ini_action->cmd_count; ++i_cmd)
          {
            const char* cmd = ini_action->cmd[i_cmd];
            if(cstr_eq(cmd, ">"))
            {
              i_cmd++;
              if(i_cmd == ini_action->cmd_count)
                PANIC("Missing filepath after `>`");
              if(i_cmd+1 != ini_action->cmd_count)
                PANIC("Expecting no more than one filepath after `>`");
              const char* cmd = ini_action->cmd[i_cmd];
              cc.capture_run_stdout = true;
              cc.capture_run_stdout_filepath = path_join(dir, path_from_cstr(cmd));
            }
            else
              cc.run_args_count++;
          }
          break;
        }
        else
          PANIC("Unexpected argument: ```\n%s\n```\n", cmd);
      }

#if 0
      {
        char buf[4096];
        Fmt f = fmt_new(buf, sizeof(buf));
        cc_command_fmt(&f, cc);
        printf("%s\n", f.begin);
      }
#endif

      action->cc = cc;
    }
  }

  if(cfg->action == USIZE_MAX && project.action_count==1)
    cfg->action = 0;

  return project;
}
