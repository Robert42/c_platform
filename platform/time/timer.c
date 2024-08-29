// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "timer.h"

u64 timer_freq;

const char* time_format_short_duration(u64 time, Mem_Region* region)
{
  long double seconds = (long double)time / (long double)timer_freq;

  const char* unit = NULL;
  bool two_digits = false;

  if(seconds >= 1)
  {
    unit = "s";
    two_digits = true;
  }else if(seconds*1000 >= 1)
  {
    seconds *= 1000;
    unit = "ms";
  }else if(seconds*1000*1000 >= 1)
  {
    seconds *= 1000 * 1000;
    unit = "us";
  }else
  {
    seconds *= 1000 * 1000 * 1000;
    unit = "ns";
  }

  char* text = (char*)region->begin;
  const usize available = mem_region_available_bytes(region);

  const int formatted_len = two_digits
                            ? snprintf(text, available, "%.2f %s", (double)seconds, unit)
                            : snprintf(text, available, "%.0f %s", (double)seconds, unit);
  assert_usize_lte_lt(0, formatted_len, available); // out of memory?

  region->begin += formatted_len + 1;
  debug_assert_usize_eq(formatted_len, strlen(text));

  return text;
}
