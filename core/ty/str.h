// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

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
#define STR_LIT(XS) str_from_cstr_len(XS, ARRAY_LEN(XS)-1)

str str_from_cstr(const char* s);

/*@
  requires str_valid(x) && str_valid(y);
  assigns \nothing;
  ensures \result == 0 ==> str_len(x) == str_len(y) && x.begin[0 .. str_len(x)-1] == y.begin[0 .. str_len(y)-1];
  ensures \result < 0 ==>
    (str_len(x) < str_len(y) && x.begin[0 .. str_len(x)-1] == y.begin[0 .. str_len(x)-1]) ||
    (\exists usize i; 0 <= i < str_len(x)-1 && 0 <= i < str_len(y)-1 ==> x.begin[0 .. i-1] == y.begin[0 .. i-1] && x.begin[i] < y.begin[i]);
  ensures \result > 0 ==>
    (str_len(x) > str_len(y) && x.begin[0 .. str_len(y)-1] == y.begin[0 .. str_len(y)-1]) ||
    (\exists usize i; 0 <= i < str_len(x)-1 && 0 <= i < str_len(y)-1 ==> x.begin[0 .. i-1] == y.begin[0 .. i-1] && x.begin[i] > y.begin[i]);
*/
int str_cmp(str x, str y);
int str_cstr_cmp(str x, const char* y);

bool str_ends_with(str haystack, str needle);

str str_trim_right(str xs);

char* str_fmt_to_region(Mem_Region* region, str x);
char* str_fmt(str x);

/*@
  assigns *region \from fmt;
  assigns \result \from *region;
*/
char* cstr_fmt(Mem_Region* region, const char* fmt, ...) ATT_PRINTF(2, 3);

/*@
  assigns *region \from fmt, args;
  assigns \result \from *region;
*/
char* cstr_fmt_va(Mem_Region* region, const char* fmt, va_list args);

