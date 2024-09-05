// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "timer.h"

u64 timer_freq;

// TODO: move to utils?
char* cstr_fmt(Mem_Region* region, const char* fmt, ...);
char* time_format_short_duration(u64 time, Mem_Region* region)
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

  return two_digits
          ? cstr_fmt(region, "%.2f %s", (double)seconds, unit)
          : cstr_fmt(region, "%.0f %s", (double)seconds, unit);
}
