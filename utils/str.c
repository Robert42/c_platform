// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "str.h"

char* str_fmt(Mem_Region* region, const char* fmt, ...)
{
  va_list args;
  va_start(args, fmt);
  const char* result = str_fmt_va(region, fmt, args);
  va_end(args);
}

char* str_fmt_va(Mem_Region* region, const char* fmt, va_list args)
{
  char* const begin = region->begin;
  const usize available_bytes = mem_region_available_bytes(region);

  const ssize actual_len = vsnprintf(begin, available_bytes, fmt, args);

  assert_ssize_gte(actual_len, 0);
  assert_ssize_lte((usize)actual_len, available_bytes); // we already know actual_len is >= 0

  region->begin += (usize)actual_len + 1;
  return begin;
}
