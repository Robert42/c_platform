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

Path LOG_DIR;

char* frama_c_log_file(const char* plugin_name, const char* suffix)
{
  return str_fmt(&PERSISTENT, "%s/frama_c.%s%s.log", LOG_DIR.cstr, plugin_name, suffix);
}

int main(int argc, const char** argv)
{
  c_script_init();
  
  const Path dir = path_parent(path_realpath(path_from_cstr(__FILE__)));
  const Path all_tests_bin_path = path_join(dir, path_from_cstr("all_tests"));
  const Path all_tests_src_path = path_append_cstr(all_tests_bin_path, ".c");

  LOG_DIR = path_join(dir, path_append_cstr(path_from_cstr(time_format_date_time_now(&SCRATCH)), ".log"));
  LINUX_ASSERT_NE(mkdir(LOG_DIR.cstr, 0777), -1);


  printf("%s", TERM_CLEAR);
  fflush(stdout);

  printf("%s==== static analysis ====%s\n", TERM_HEADER, TERM_NORMAL);

  const Path frama_c_ast = path_join(LOG_DIR, path_from_cstr("frama_c_parse.sav"));
  {
    const char* const log_err = frama_c_log_file("kernel", ".err");
    const char* const log_warn = frama_c_log_file("kernel", ".warn");
    char* const cmd_parse[] = {"frama-c", all_tests_src_path.cstr, "-kernel-log", str_fmt(&SCRATCH, "e:%s,w:%s", log_err, log_warn), "-save", frama_c_ast.cstr, NULL};

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
    char* const cmd_eva[] = {"frama-c", "-load", frama_c_ast.cstr, "-eva-log", str_fmt(&SCRATCH, "e:%s,w:%s%s", log_err, log_warn), "-eva-precision", "3", "-eva", NULL};

    struct Cmd cmd = {
      .name = "frama_c.eva",
      .cmd = cmd_eva,
      .log_err = log_err,
      .log_warn = log_warn,
    };
    cmd_exec(cmd);
  }


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

  if(!ok)
    exit(EXIT_FAILURE);
}
