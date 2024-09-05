// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct _utils_str;
typedef struct _utils_str str;

struct _utils_str
{
  const char* begin;
  const char* end;
};

/*@
  logic integer str_len(str s) = s.end - s.begin;
  predicate str_valid(str s) = 
    s.begin <= s.end &&
    (usize)(s.end - s.begin) == s.end - s.begin &&
    \valid_read(s.begin + (0 .. str_len(s)-1));
*/

/*@
  requires str_valid(s);
  assigns \nothing;
  ensures \result == str_len(s);
*/
usize str_len(str s);

/*@
  requires \valid(s + (0 .. len-1));
  assigns \nothing;
  ensures valid: str_valid(\result);
  ensures same_len: str_len(\result) == len;
  ensures same_content: \result.begin[0 .. len-1] == s[0 .. len-1];
  ensures aliasing: \result.begin == s && \result.end == s+len;
*/
str str_from_cstr_len(const char* s, usize len);

// TODO: tell the compilers & analyzers, that this is using printf formatting
/*@
  assigns *region \from fmt;
  assigns \result \from *region;
*/
char* cstr_fmt(Mem_Region* region, const char* fmt, ...);

/*@
  assigns *region \from fmt, args;
  assigns \result \from *region;
*/
char* cstr_fmt_va(Mem_Region* region, const char* fmt, va_list args);

