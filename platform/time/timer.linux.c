// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "timer.h"

static u64 _linux_timespect_to_nsec(struct timespec t)
{
  const u64 usec_in_nsec = 1000;
  const u64 msec_in_nsec = 1000 * usec_in_nsec;
  const u64 sec_in_nsec = 1000 * msec_in_nsec;
  return (u64)t.tv_nsec + sec_in_nsec * (u64)t.tv_sec;
}

#define CLOCK CLOCK_MONOTONIC

u64 timer_now()
{
  struct timespec t;
  LINUX_ASSERT_NE(clock_gettime(CLOCK, &t), -1);

  return _linux_timespect_to_nsec(t);
}

void timer_init()
{
  // I do not get the resolution, because _linux_timespect_to_nsec doesn't need
  // the resolution to translate `struct timespec` values to seconds.

  timer_freq = _linux_timespect_to_nsec((struct timespec){.tv_sec=1});
}

#undef CLOCK

char* time_format_date_time_now(Mem_Region* region)
{
  char* const args[] = {"date", "+%Y-%m-%d_%H-%M-%S", NULL};
  struct Proc_Exec_Blocking_Settings settings = {
    .capture_stdout = true,
    .capture_stderr = true,
    .region_stdout = region,
  };
  struct Proc_Exec_Blocking_Result result = proc_exec_blocking(args, settings);
  LINUX_ASSERT_EQ(result.success, true);

  cstr_trim_right(result.captured_stdout);

  return result.captured_stdout;
}

