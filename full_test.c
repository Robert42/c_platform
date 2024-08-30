// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "c_script.h"

#define TERM_HEADER TERM_NORMAL

struct Cmd
{
  const char* name;
  char* const * cmd;

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
  return str_fmt(&PERSISTENT, "%s/frama_c.%s%s.log", LOG_DIR.cstr, plugin_name, suffix);
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


  printf("%s", TERM_CLEAR);
  fflush(stdout);

  printf("%s==== static analysis ====%s\n", TERM_HEADER, TERM_NORMAL);

  const Path frama_c_ast = path_join(LOG_DIR, path_from_cstr("frama_c_parse.sav"));
  {
    const char* const log_err = frama_c_log_file("kernel", ".err");
    const char* const log_warn = frama_c_log_file("kernel", ".warn");
    char* const cmd_parse[] = {"frama-c", src_c_path(SRC_ALL_TEST).cstr, "-kernel-log", str_fmt(&SCRATCH, "e:%s,w:%s", log_err, log_warn), "-save", frama_c_ast.cstr, NULL};

    struct Cmd cmd = {
      .name = "frama_c.parse",
      .cmd = cmd_parse,
      .log_err = log_err,
      .log_warn = log_warn,
    };
    cmd_exec(cmd);
  }
  {
    const char* const log_err = frama_c_log_file("kernel", ".err");
    const char* const log_warn = frama_c_log_file("kernel", ".warn");
    char* const cmd_eva[] = {"frama-c", "-load", frama_c_ast.cstr, "-eva-log", str_fmt(&SCRATCH, "e:%s,w:%s", log_err, log_warn), "-eva-precision", "3", "-eva", NULL};

    struct Cmd cmd = {
      .name = "frama_c.eva",
      .cmd = cmd_eva,
      .log_err = log_err,
      .log_warn = log_warn,
    };
    cmd_exec(cmd);
  }

  printf("%s==== compilers ====%s\n", TERM_HEADER, TERM_NORMAL);
  for(int cc_idx=0; cc_idx<CC_COUNT; ++cc_idx)
  {
    enum C_Compiler cc = (enum C_Compiler)cc_idx;
    const char* const compiler_name = cc_compiler_name(cc);
    if(!cc_compiler_is_available(cc))
      continue;

    printf("%s== %s%s\n", TERM_HEADER, compiler_name, TERM_NORMAL);
    
    for(int src_idx=0; src_idx<SRC_COUNT; ++src_idx)
    {
      const Path output_file = src_bin_path(src_idx);
      const Path c_file = src_c_path(src_idx);
      
      {
        char* const cmd_compile_tcc[] = {"tcc", "-Wall", c_file.cstr, "-o", output_file.cstr, NULL};
        char* const cmd_compile_gcc[] = {"gcc", "-std=c99", "-Wall", "-pedantic", c_file.cstr, "-o", output_file.cstr, NULL};
        char* const cmd_compile_clang[] = {"clang", "-std=c99", "-Wall", "-pedantic", c_file.cstr, "-o", output_file.cstr, NULL};

        char* const * cmd_compile[] = {
          [CC_TCC] = cmd_compile_tcc,
          [CC_GCC] = cmd_compile_gcc,
          [CC_CLANG] = cmd_compile_clang,
        };

        struct Cmd cmd = {
          .name = str_fmt(&SCRATCH, "%s (compile)", SRC_BASENAME[src_idx]),
          .cmd = cmd_compile[cc],
          .err_text = "error:",
        };
        cmd_exec(cmd);
      }

      {
        char* const cmd_test[] = {output_file.cstr, NULL};
        struct Cmd cmd = {
          .name = SRC_BASENAME[src_idx],
          .cmd = cmd_test,
        };
        cmd_exec(cmd);
      }
    }
  }

  if(HAD_WARNING)
    printf("%s==== DONE (with %sWARNING%ss) ====%s\n", TERM_YELLOW, TERM_YELLOW_BOLD, TERM_YELLOW, TERM_NORMAL);
  else
    printf("%s==== DONE ====%s\n", TERM_GREEN_BOLD, TERM_NORMAL);

  return EXIT_SUCCESS;
}

static void print_result(const char* style_name, const char* name, const char* style_result, const char* result, const char* duration)
{
  printf("%s%s%s%s %s%s (%s)%s\n", TERM_CLEAR_LINE, style_name, name, style_result, result, style_name, duration, TERM_NORMAL);
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
  if(TERM_CLEAR_LINE[0])
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
    && (cmd.err_text == NULL || !strstr(result.captured_stdout, cmd.err_text));
  const bool warning =
       (cmd.log_warn != NULL && _file_size(cmd.log_warn)>0)
    || (cmd.warning_text != NULL && strstr(result.captured_stdout, cmd.warning_text));

  const char* const duration = time_format_short_duration(time_end-time_begin, &SCRATCH);
  if(ok && warning)
    print_result(TERM_YELLOW, cmd.name, TERM_YELLOW_BOLD, "WARNING", duration);
  else if(ok)
    print_result(TERM_GREEN, cmd.name, TERM_GREEN_BOLD, "OK", duration);
  else
    print_result(TERM_RED, cmd.name, TERM_RED_BOLD, "FAILED", duration);

  const Path log_path = path_join(LOG_DIR, path_from_cstr(cmd.name));
  if(result.captured_stdout[0] != 0)
    create_text_file_cstr(path_append_cstr(log_path, ".stdout.log"), result.captured_stdout);
  if(result.captured_stderr[0] != 0)
    create_text_file_cstr(path_append_cstr(log_path, ".stderr.log"), result.captured_stderr);

  HAD_WARNING = HAD_WARNING || warning;

  if(!ok)
    exit(EXIT_FAILURE);
}
