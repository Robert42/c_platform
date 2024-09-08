// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "c_script.h"

#define TERM_HEADER TERM.normal

#define OPEN_GUI 1
struct Cmd
{
  const char* name;
  char* const * cmd;
  char* const * cmd_open_gui;

  const char* err_text;
  const char* warning_text;

  const char* log_err;
  const char* log_warn;
};
static void cmd_exec(struct Cmd cmd);

Path DIR;
Path LOG_DIR;
bool HAD_WARNING = false;

char* frama_c_log_file(const char* plugin_name, const char* suffix)
{
  return cstr_fmt(&PERSISTENT, "%s/frama_c.%s%s.log", LOG_DIR.cstr, plugin_name, suffix);
}

enum Src_File
{
  SRC_ALL_TEST,
};
const char* SRC_BASENAME[] = {
  [SRC_ALL_TEST] = "all_tests",
};
#define SRC_COUNT (ARRAY_LEN(SRC_BASENAME))
Path src_bin_path(enum Src_File s)
{
  return path_join(DIR, path_from_cstr(SRC_BASENAME[s]));
}
Path src_c_path(enum Src_File s)
{
  return path_append_cstr(src_bin_path(s), ".c");
}

int main(int argc, const char** argv)
{
  c_script_init();

  DIR = path_parent(path_realpath(path_from_cstr(__FILE__)));
  LOG_DIR = path_join(DIR, path_append_cstr(path_from_cstr(time_format_date_time_now(&SCRATCH)), ".log"));
  LINUX_ASSERT_NE(mkdir(LOG_DIR.cstr, 0777), -1);

  printf("%s", TERM.clear);
  fflush(stdout);

#if 0 // ISSUE_FRAMA_C: decide, whether to keep frama-c
  printf("%s==== static analysis ====%s\n", TERM_HEADER, TERM.normal);

  Path frama_c_prev_stage;
  {
    const Path frama_c_kernel_sav = path_join(LOG_DIR, path_from_cstr("frama_c_parse.sav"));
    const char* const log_err = frama_c_log_file("kernel", ".err");
    const char* const log_warn = frama_c_log_file("kernel", ".warn");
    char* const cmd_parse[] = {"frama-c",
      src_c_path(SRC_ALL_TEST).cstr,
      "-kernel-log", cstr_fmt(&SCRATCH, "e:%s,w:%s", log_err, log_warn),
      "-save", frama_c_kernel_sav.cstr,
      NULL};

    struct Cmd cmd = {
      .name = "frama_c.parse",
      .cmd = cmd_parse,
      .log_err = log_err,
      .log_warn = log_warn,
    };
    cmd_exec(cmd);
    frama_c_prev_stage = frama_c_kernel_sav;
  }
  {
#define WP_WARNINGS

    const Path frama_c_wp_sav = path_join(LOG_DIR, path_from_cstr("frama_c.wp.sav"));
    const char* const log_err = frama_c_log_file("wp", ".err");
    const char* const log_warn = frama_c_log_file("wp", ".warn");
    char* const cmd_wp[] = {"frama-c",
      "-load", frama_c_prev_stage.cstr,
      WP_WARNINGS
      "-wp-log", cstr_fmt(&SCRATCH, "e:%s,w:%s", log_err, log_warn),
      "-wp",
      "-rte",
      "-save", frama_c_wp_sav.cstr,
      NULL};
    char* const cmd_open_frama_c_gui[] = {"frama-c-gui",
      "-load", frama_c_wp_sav.cstr,
      NULL};

    struct Cmd cmd = {
      .name = "frama_c.wp",
      .cmd = cmd_wp,
      .cmd_open_gui = cmd_open_frama_c_gui,
      .log_err = log_err,
      .log_warn = log_warn,
    };
    cmd_exec(cmd);
    frama_c_prev_stage = frama_c_wp_sav;
#undef WP_WARNINGS
  }
  {
#define EVA_WARNINGS \
    "-unspecified-access", /* Book 2.4.1 p.100, reason why it is disabled by default on page 108 */ \
    "-warn-signed-downcast", /* Book p.103 */ \

    const Path frama_c_eva_sav = path_join(LOG_DIR, path_from_cstr("frama_c.eva.sav"));
    const char* const log_err = frama_c_log_file("eva", ".err");
    const char* const log_warn = frama_c_log_file("eva", ".warn");
    char* const cmd_eva[] = {"frama-c",
      "-load", frama_c_prev_stage.cstr,
      EVA_WARNINGS
      "-eva-log", cstr_fmt(&SCRATCH, "e:%s,w:%s", log_err, log_warn),
      "-eva-precision", "3",
      "-eva",
      "-save", frama_c_eva_sav.cstr,
      NULL};
    char* const cmd_open_frama_c_gui[] = {"frama-c-gui",
      "-load", frama_c_eva_sav.cstr,
      NULL};

    struct Cmd cmd = {
      .name = "frama_c.eva",
      .cmd = cmd_eva,
      .cmd_open_gui = cmd_open_frama_c_gui,
      .log_err = log_err,
      .log_warn = log_warn,
    };
    cmd_exec(cmd);
    frama_c_prev_stage = frama_c_eva_sav;
#undef EVA_WARNINGS
  }
  #endif

  printf("%s==== compilers ====%s\n", TERM_HEADER, TERM.normal);
  for(int cc_idx=0; cc_idx<CC_COUNT; ++cc_idx)
  {
    enum C_Compiler cc = (enum C_Compiler)cc_idx;
    const char* const compiler_name = cc_compiler_name(cc);
    if(!cc_compiler_is_available(cc))
      continue;

    printf("%s== %s%s\n", TERM_HEADER, compiler_name, TERM.normal);
    
    for(int src_idx=0; src_idx<SRC_COUNT; ++src_idx)
    {
      const Path output_file = src_bin_path(src_idx);
      const Path c_file = src_c_path(src_idx);
      
      char* const cmd_compile_tcc[] = {"tcc",
        "-Wall",
        c_file.cstr,
        "-o", output_file.cstr,
        NULL};
      char* const cmd_compile_gcc[] = {"gcc",
        "-std=c99",
        "-g",
        GCC_WARNING_OPTIONS
        GCC_SANITIZER_OPTIONS
        c_file.cstr,
        "-o", output_file.cstr,
        NULL};
      char* const cmd_compile_clang[] = {"clang",
        "-std=c99",
        "-g",
        GCC_WARNING_OPTIONS
        GCC_SANITIZER_OPTIONS
        c_file.cstr,
        "-o", output_file.cstr,
        NULL};

      char* const * cmd_compile[CC_COUNT] = {
        [CC_TCC] = cmd_compile_tcc,
        [CC_GCC] = cmd_compile_gcc,
        [CC_CLANG] = cmd_compile_clang,
      };
      bool has_sanitizer[CC_COUNT] = {
        [CC_TCC] = false,
        [CC_GCC] = true,
        [CC_CLANG] = true,
      };
      bool incompatible_to_valgrind[CC_COUNT] = {
        [CC_TCC] = ENV_ARCH==ARCH_AARCH64,
      };

      {
        struct Cmd cmd = {
          .name = cstr_fmt(&SCRATCH, "%s (compile with %s)", SRC_BASENAME[src_idx], cmd_compile[cc][0]),
          .cmd = cmd_compile[cc],
          .err_text = "error:",
          .warning_text = "warning:",
        };
        cmd_exec(cmd);
      }

      {
        char* const cmd_test[] = {output_file.cstr, NULL};
        struct Cmd cmd = {
          .name = cstr_fmt(&SCRATCH, "%s (%s)", SRC_BASENAME[src_idx], cmd_compile[cc][0]),
          .cmd = cmd_test,
        };
        cmd_exec(cmd);
      }

      if(has_sanitizer[cc])
      {
        // disable the sanitizer
        char* const cmd_compile_without_sanitizer[] = {cmd_compile[cc][0],
          "-std=c99",
          "-g",
          GCC_WARNING_OPTIONS
          c_file.cstr,
          "-o", output_file.cstr,
          NULL};

        // recompile unsanitized
        {
          struct Cmd cmd = {
            .name = cstr_fmt(&SCRATCH, "%s (recompile with %s and without sanitizers)", SRC_BASENAME[src_idx], cmd_compile_without_sanitizer[0]),
            .cmd = cmd_compile_without_sanitizer,
            .err_text = "error:",
            .warning_text = "warning:",
          };
          cmd_exec(cmd);
        }
      }

      if(!incompatible_to_valgrind[cc])
      {
        char* const cmd_test[] = {"valgrind",
          "--leak-check=full",
          "--error-exitcode=1",
          output_file.cstr,
          NULL};
        struct Cmd cmd = {
          .name = cstr_fmt(&SCRATCH, "valgrind %s (%s)", SRC_BASENAME[src_idx], cmd_compile[cc][0]),
          .cmd = cmd_test,
          .warning_text = "WARNING:",
        };
        cmd_exec(cmd);
      }
    }
  }

  if(HAD_WARNING)
    printf("%s==== DONE (with %sWARNING%ss) ====%s\n", TERM.yellow, TERM.yellow_bold, TERM.yellow, TERM.normal);
  else
    printf("%s==== DONE ====%s\n", TERM.green_bold, TERM.normal);

  return EXIT_SUCCESS;
}

static void print_result(const char* style_name, const char* name, const char* style_result, const char* result, const char* duration)
{
  printf("%s%s%s%s %s%s (%s)%s\n", TERM.clear_line, style_name, name, style_result, result, style_name, duration, TERM.normal);
  fflush(stdout);
}

static void cmd_exec(struct Cmd cmd)
{
  struct Proc_Exec_Blocking_Settings capture_everything = {
    .capture_stdout = true,
    .capture_stderr = true,
    .region_stdout = &SCRATCH,
    .region_stderr = &SCRATCH,
  };

  // if te result is printed in a terminal, show what we are running while we are running
  if(TERM.clear_line[0])
  {
    printf("%s ...", cmd.name);
    fflush(stdout);
  }

  const u64 time_begin = timer_now();
  struct Proc_Exec_Blocking_Result result = proc_exec_blocking(cmd.cmd, capture_everything);
  const u64 time_end = timer_now();
  const bool ok =
    result.exit_code == EXIT_SUCCESS
    && (cmd.log_err == NULL || _file_size(cmd.log_err)<=0)
    && (cmd.err_text == NULL || !strstr(result.captured_stderr, cmd.err_text))
    && (cmd.err_text == NULL || !strstr(result.captured_stdout, cmd.err_text));
  const bool warning =
       (cmd.log_warn != NULL && _file_size(cmd.log_warn)>0)
    || (cmd.warning_text != NULL && strstr(result.captured_stderr, cmd.warning_text))
    || (cmd.warning_text != NULL && strstr(result.captured_stdout, cmd.warning_text));

  const char* const duration = time_format_short_duration(time_end-time_begin, &SCRATCH);
  if(ok && warning)
    print_result(TERM.yellow, cmd.name, TERM.yellow_bold, "WARNING", duration);
  else if(ok)
    print_result(TERM.green, cmd.name, TERM.green_bold, "OK", duration);
  else
    print_result(TERM.red, cmd.name, TERM.red_bold, "FAILED", duration);

  const Path log_path = path_join(LOG_DIR, path_from_cstr(cmd.name));
  if(result.captured_stdout[0] != 0)
    file_text_create_from_cstr(path_append_cstr(log_path, ".stdout.log"), result.captured_stdout);
  if(result.captured_stderr[0] != 0)
    file_text_create_from_cstr(path_append_cstr(log_path, ".stderr.log"), result.captured_stderr);

  HAD_WARNING = HAD_WARNING || warning;

#if OPEN_GUI
  if((warning||!ok) && cmd.cmd_open_gui!=NULL)
  {
    struct Proc_Exec_Blocking_Settings block = {
      // .capture_stdout = true,
      // .capture_stderr = true,
    };
    proc_exec_blocking(cmd.cmd_open_gui, block);
  }
#endif

  if(!ok)
    exit(EXIT_FAILURE);
}
