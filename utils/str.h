// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

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

/*@
  requires str_valid(x) && str_valid(y);
  assigns \nothing;
  behavior eq:
    requires str_len(x) == str_len(y);
    requires x.begin[0 .. str_len(x)-1] == y.begin[0 .. str_len(y)-1];
    ensures \result == 0;
  behavior lt_content:
    requires \exists usize n; n<str_len(x) && n<str_len(y) ==> x.begin[0 .. n-1] == y.begin[0 .. n-1] && x.begin[n] < y.begin[n];
    ensures \result < 0;
  behavior lt_len:
    requires str_len(x) < str_len(y);
    requires x.begin[0 .. str_len(x)-1] == y.begin[0 .. str_len(x)-1];
    ensures \result < 0;
  behavior gt_content:
    requires \exists usize n; n<str_len(x) && n<str_len(y) ==> x.begin[0 .. n-1] == y.begin[0 .. n-1] && x.begin[n] > y.begin[n];
    ensures \result > 0;
  behavior gt_len:
    requires str_len(x) > str_len(y);
    requires x.begin[0 .. str_len(y)-1] == y.begin[0 .. str_len(y)-1];
    ensures \result > 0;
  complete behaviors;
  disjoint behaviors;
*/
int str_cmp(str x, str y);

const char* str_fmt(str x);

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

