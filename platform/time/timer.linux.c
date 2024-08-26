// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "timer.h"

static u64 _linux_timespect_to_nsec(struct timespec t)
{
  const u64 usec_in_nsec = 1000;
  const u64 msec_in_nsec = 1000 * usec_in_nsec;
  const u64 sec_in_nsec = 1000 * msec_in_nsec;
  return (u64)t.tv_nsec + sec_in_nsec * (u64)t.tv_sec;
}

#define CLOCK CLOCK_MONOTONIC_RAW

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

  timer_freq = 1000000000;
}

#undef CLOCK
