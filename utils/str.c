// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "str.h"

#ifndef __FRAMAC__ // TODO
char* cstr_fmt(Mem_Region* region, const char* fmt, ...)
{
  va_list args;
  va_start(args, fmt);
  char* result = cstr_fmt_va(region, fmt, args);
  va_end(args);
  return result;
}

char* cstr_fmt_va(Mem_Region* region, const char* fmt, va_list args)
{
  char* const begin = (const char*)region->begin;
  const usize available_bytes = mem_region_available_bytes(*region);

  const ssize actual_len = vsnprintf(begin, available_bytes, fmt, args);

  assert_ssize_gte(actual_len, 0);
  assert_ssize_lte((usize)actual_len, available_bytes); // we already know actual_len is >= 0

  region->begin += (usize)actual_len + 1;
  return begin;
}
#endif // __FRAMA_C__ // TODO
