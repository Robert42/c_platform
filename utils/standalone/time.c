// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

// Custom implementation of the bash command `time`
// ```
// gcc -O2 ./utils/standalone/time.c -o ./utils/standalone/time
// ```

#include "../../c_script.h"

int main(int argc, char** argv)
{
  (void)argc;
  (void)argv;
  c_script_init();

  const u64 time_begin = timer_now();
  struct Proc_Exec_Blocking_Result result = proc_exec_blocking(argv + 1, (struct Proc_Exec_Blocking_Settings){0});
  const u64 time_end = timer_now();

  const char* duration = time_format_short_duration(time_end-time_begin, &SCRATCH);

  printf("\n%s==== time: %s%s%s ====%s\n", TERM.green, TERM.green_bold, duration, TERM.green, TERM.normal);

  return result.exit_code;
}

