// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "str.h"

usize str_len(str s)
{
  debug_assert_ptr_lte(s.begin, s.end);
  const ssize len = s.end - s.begin;
  //@assert len >= 0;
  return len;
}

str str_from_cstr_len(const char* s, usize len)
{
  return (str){s, s+len};
}

// TODO move elsewhere
/*@
  assigns \nothing;
  ensures \result <= x;
  ensures \result <= y;
  ensures \result==x || \result==y;
*/
usize min_usize(usize x, usize y)
{
  return x < y ? x : y;
}

int str_cmp(str x, str y)
{
  const usize x_len = str_len(x);
  const usize y_len = str_len(y);
  const usize len = min_usize(x_len, y_len);

  /*@
    loop assigns \nothing;
  */
  for(usize i=0; i<len; ++i)
    if(x.begin[i] != y.begin[i])
      return x.begin[i] - y.begin[i];

  return x_len - y_len;
}

#ifndef __FRAMAC__ // TODO
const char* str_fmt(str x)
{
  usize len = str_len(x);
  char* const copy = (char*)mem_region_alloc_bytes_unaligned(&SCRATCH, len+1);
  copy[len] = 0;
  memcpy(copy, x.begin, len);
  return copy;
}

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
  char* const begin = (char*)region->begin;
  const usize available_bytes = mem_region_available_bytes(*region);

  const ssize actual_len = vsnprintf(begin, available_bytes, fmt, args);

  assert_ssize_gte(actual_len, 0);
  assert_ssize_lte((usize)actual_len, available_bytes); // we already know actual_len is >= 0

  region->begin += (usize)actual_len + 1;
  return begin;
}
#endif // __FRAMA_C__ // TODO
