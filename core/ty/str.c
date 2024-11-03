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

str str_from_cstr(const char* s)
{
  return str_from_cstr_len(s, strlen(s));
}

int str_cmp(str x, str y)
{
  const usize x_len = str_len(x);
  const usize y_len = str_len(y);
  const usize len = min_usize(x_len, y_len);

  /*@
    loop assigns i;
    loop invariant 0 <= i <= len;
    loop invariant x.begin[0 .. i-1] == y.begin[0 .. i-1];
    loop variant len - i;
  */
  for(usize i=0; i<len; ++i)
  {
    const char x_char = x.begin[i];
    const char y_char = y.begin[i];
    if(x_char != y_char)
    {
      //@ assert x_char - y_char != 0;
      //@ assert x.begin[0 .. i-1] == y.begin[0 .. i-1];
      return x_char - y_char;
    }
  }

  //@ assert x.begin[0 .. len-1] == y.begin[0 .. len-1];
  if(x_len < y_len) return -1;
  if(x_len > y_len) return 1;
  return 0;
}

int str_cstr_cmp(str x, const char* y)
{
  return str_cmp(x, (str){y, y+strlen(y)});
}

bool str_ends_with(str haystack, str needle)
{
  const usize needle_len = str_len(needle);
  if(str_len(haystack) < needle_len)
    return false;

  return str_cmp((str){haystack.end-needle_len, haystack.end}, needle) == 0;
}

str str_trim_right(str xs)
{
  while(xs.begin < xs.end && char_is_ws(xs.end[-1]))
    xs.end--;
  return xs;
}

#ifndef __FRAMAC__ // ISSUE_FRAMA_C
char* str_fmt_to_region(Mem_Region* region, str x)
{
  usize len = str_len(x);
  char* const copy = (char*)mem_region_alloc_bytes_unaligned(region, len+1);
  copy[len] = 0;
  memcpy(copy, x.begin, len);
  return copy;
}

char* str_fmt(str x)
{
  return str_fmt_to_region(&SCRATCH, x);
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
#endif // __FRAMA_C__ // ISSUE_FRAMA_C

