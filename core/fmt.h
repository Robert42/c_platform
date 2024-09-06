// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

typedef struct _utils_Fmt
{
  char* begin; // also the beginning of the buffer
  usize buffer_capacity;
  char* end;

#if GHOST
  ssize available_bytes;
#endif
} Fmt;

/*@
    logic integer _logic_fmt_used_chars(Fmt f) = f.end-f.begin;
    logic integer _logic_fmt_availalbe_chars(Fmt f) = f.buffer_capacity - _logic_fmt_used_chars(f);

    predicate fmt_valid(Fmt f) =
  \valid(f.begin + (0 .. f.buffer_capacity-1))
  && \offset(f.begin)+f.buffer_capacity <= \block_length(f.begin)
  && f.begin <= f.end < f.begin+f.buffer_capacity
  && f.buffer_capacity > 0
  && f.end[0] == 0 // So f.begin is always a valid nullterminated cstr
  && 0 <= f.available_bytes == _logic_fmt_availalbe_chars(f)
  && f.buffer_capacity == (ssize)f.buffer_capacity
  && f.available_bytes <= f.buffer_capacity
  && f.end+f.available_bytes == f.begin+f.buffer_capacity
  && 0 <= _logic_fmt_used_chars(f) <= f.buffer_capacity
  && 0 <= _logic_fmt_used_chars(f) + _logic_fmt_availalbe_chars(f) == f.buffer_capacity
;
*/

Fmt fmt_new(char* buffer, usize capacity);
void fmt_write(Fmt* f, const char* text, ...);

