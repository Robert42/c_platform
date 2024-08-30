// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "platform/platform.c"
#include "utils/utils.c"

#include "platform/test.c"
#include "utils/test.c"

static u8 _SCRATCH_BUFFER_1[1024*1024] = {0};
Mem_Region SCRATCH = {0};

#define TERM_HEADER TERM_NORMAL

struct Cmd
{
  const char* name;
  char* const * cmd;

  const char* err_text;
  const char* warning_text;
};
static void cmd_exec(struct Cmd cmd);

Path LOG_DIR;

char* frama_c_opt_log(const char* plugin_name)
{
  return str_fmt(&SCRATCH, "e:%s/frama_c.%s.err.log,w:%s/frama_c.%s.warn.log", LOG_DIR.cstr, plugin_name, LOG_DIR.cstr, plugin_name);
}

int main(int argc, const char** argv)
{
  platform_init();
  
  const Path full_test_file = path_realpath(path_from_cstr(__FILE__));

  SCRATCH = MEM_REGION_FROM_ARRAY(_SCRATCH_BUFFER_1);

  LOG_DIR = path_join(path_parent(full_test_file), path_append_cstr(path_from_cstr(time_format_date_time_now(&SCRATCH)), ".log"));
  LINUX_ASSERT_NE(mkdir(LOG_DIR.cstr, 0777), -1);

  printf("%s", TERM_CLEAR);
  fflush(stdout);

  printf("%s==== static analysis ====%s\n", TERM_HEADER, TERM_NORMAL);

  const Path frama_c_ast = path_join(LOG_DIR, path_from_cstr("frama_c_parse.sav"));
  {
    char* const cmd_parse[] = {"frama-c", full_test_file.cstr, "-kernel-log", frama_c_opt_log("kernel"), "-save", frama_c_ast.cstr, NULL};

    struct Cmd cmd = {
      .name = "frama_c.parse",
      .cmd = cmd_parse,
      .warning_text = "Warning:",
      .err_text = "error:",
    };
    cmd_exec(cmd);
  }
  {
    char* const cmd_eva[] = {"frama-c", "-load", frama_c_ast.cstr, "-eva-log", frama_c_opt_log("eva"), "-eva-precision", "3", "-eva", NULL};

    struct Cmd cmd = {
      .name = "frama_c.eva",
      .cmd = cmd_eva,
      .warning_text = "Warning:",
      .err_text = "error:",
    };
    cmd_exec(cmd);
  }

  printf("%s==== run tests ====%s\n", TERM_HEADER, TERM_NORMAL);
  platform_test();
  utils_test();

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
  bool ok;
  bool warning = cmd.warning_text != NULL && strstr(result.captured_stdout, cmd.warning_text);
  if(result.exit_code != EXIT_SUCCESS)
    ok = false;
  else if(cmd.err_text != NULL)
    ok = !strstr(result.captured_stdout, cmd.err_text);
  else
    ok = true;

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
