// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "fmt.h"

/*@ requires fmt_valid(f);
    assigns \nothing;
    ensures \result == _logic_fmt_availalbe_chars(f);
*/
static inline usize _fmt_available_chars(Fmt f)
{
  return f.buffer_capacity - (f.end - f.begin);
}

/*@ requires valid_buffer: \valid(buffer + (0 .. capacity-1));
    requires \offset(buffer)+capacity <= \block_length(buffer);
    requires capacity > 0;
    requires (ssize)capacity == capacity;
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
#if GHOST
    .available_bytes = capacity,
#endif
  };

  f.end[0] = 0;

  return f;
}

/*@ requires valid_fmt: \valid(f) && fmt_valid(*f);
    assigns f->end \from f->end, f->available_bytes;
    assigns f->end[0..f->available_bytes-1];
    assigns f->available_bytes;
    ensures fmt_valid(*f);
*/
void fmt_write(Fmt* f, const char* text, ...)
{
  usize avail = _fmt_available_chars(*f);

  va_list args;
  va_start(args, text);
  ssize bytes_written = vsnprintf(f->end, avail, text, args);
  va_end(args);
  assert_ssize_lte(0, bytes_written); // runtime error
  assert_usize_lt(bytes_written, avail); // out of memory

  f->end += bytes_written;
#if GHOST
  f->available_bytes -= bytes_written;
#endif
}

