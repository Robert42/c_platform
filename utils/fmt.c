// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "fmt.h"

/*@ requires valid_buffer: \valid(buffer + (0 .. capacity-1));
    requires \offset(buffer)+capacity <= \block_length(buffer);
    requires capacity > 0;
    assigns buffer[0];
    ensures valid: fmt_valid(\result);
    ensures all_bytes_available:\result.begin == \result.end;
*/
Fmt fmt_new(char* buffer, usize capacity)
{
  Fmt f = {
    .begin = buffer,
    .buffer_capacity = capacity,
    .end = buffer,
  };

  f.end[0] = 0;

  return f;
}

/*@ requires valid_fmt: \valid(f) && fmt_valid(*f);
    // exits format_len(text) <= ;
*/
void fmt(Fmt* f, const char* text, ...)
{
  usize avail = f->buffer_capacity - (f->begin - f->end);
  va_list args;
  va_start(args, text);
  ssize bytes_written = vsnprintf(f->end, avail, text, args);
  va_end(args);
  assert_usize_lte_lte(0, bytes_written, avail);

  f->end += bytes_written;
}
