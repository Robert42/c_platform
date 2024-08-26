// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "timer.h"

void timer_test()
{
  const u64 actual_freq = timer_freq;
  timer_freq = 500000000;

  assert_cstr_eq(time_format_short_duration(0, &SCRATCH), "0 ns");
  assert_cstr_eq(time_format_short_duration(1 * timer_freq, &SCRATCH), "1.00 s");
  assert_cstr_eq(time_format_short_duration(timer_freq/2, &SCRATCH), "500 ms");
  assert_cstr_eq(time_format_short_duration(timer_freq/2000, &SCRATCH), "500 us");

  timer_freq = actual_freq;
}
