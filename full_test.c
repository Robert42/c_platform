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
};
static void cmd_exec(struct Cmd cmd);

int main(int argc, const char** argv)
{
  platform_init();
  
  const Path full_test_file = path_from_cstr(__FILE__);

  SCRATCH = MEM_REGION_FROM_ARRAY(_SCRATCH_BUFFER_1);

  printf(TERM_CLEAR);
  fflush(stdout);


  printf("%s==== static analysis ====%s\n", TERM_HEADER, TERM_NORMAL);

  {
    char* const cmd_eva[] = {"frama-c", "-eva-precision", "3", "-eva", full_test_file.cstr, NULL};

    struct Cmd cmd = {
      .name = "frama_c.eva",
      .cmd = cmd_eva,
      .err_text = "Some errors and warnings have been raised during the analysis",
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
  printf("%s%s%s%s %s%s", TERM_CLEAR_LINE, style_name, name, style_result, result, TERM_NORMAL);
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
  if(result.exit_code != EXIT_SUCCESS)
    ok = false;
  else if(cmd.err_text != NULL)
    ok = !strstr(result.captured_stdout, cmd.err_text);
  else
    ok = true;

  const char* duration = time_format_short_duration(time_end-time_begin, &SCRATCH);
  if(ok)
  {
    print_result(TERM_GREEN, cmd.name, TERM_GREEN_BOLD, "OK", duration);
    printf(" (%s)\n", duration);
    fflush(stdout);
  }else
  {
    print_result(TERM_RED, cmd.name, TERM_RED_BOLD, "FAILED", duration);
    printf(" (after %s)\n", duration);
    fflush(stdout);
    exit(EXIT_FAILURE);
  }
}
