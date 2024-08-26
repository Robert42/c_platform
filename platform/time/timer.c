// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "timer.h"

u64 timer_freq;

const char* time_format_short_duration(u64 time, Mem_Region* region)
{
  long double seconds = (long double)time / (long double)timer_freq;

  const char* fmt = NULL;

  if(seconds >= 1)
  {
    fmt = "%.2f s";
  }else if(seconds >= 1.e-3)
  {
    seconds *= 1000;
    fmt = "%.0f ms";
  }else if(seconds >= 1.e-6)
  {
    seconds *= 1000 * 1000;
    fmt = "%.0f us";
  }else
  {
    seconds *= 1000 * 1000 * 1000;
    fmt = "%.0f ns";
  }

  const usize available = mem_region_available_bytes(region);

  const int formatted_len = snprintf(region->begin, available, fmt, (double)seconds);
  assert_usize_lte_lt(0, formatted_len, available); // out of memory?

  char* text = region->begin;
  region->begin += formatted_len + 1;
  debug_assert_usize_eq(formatted_len, strlen(text));

  return text;
}
