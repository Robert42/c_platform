// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct _utils_str;
typedef struct _utils_str str;

struct _utils_str
{
  const char* begin;
  const char* end;
};

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

