// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "fmt.h"

static inline usize _fmt_available_chars(Fmt f)
{
  return f.buffer_capacity - (f.end - f.begin);
}

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

Fmt fmt_new_from_region(Mem_Region* region, usize capacity)
{
  char* const bytes = (char*)mem_region_alloc_bytes_unaligned(region, capacity);
  Fmt f = fmt_new(bytes, capacity);
  return f;
}

void fmt_write(Fmt* f, const char* text, ...)
{
  usize avail = _fmt_available_chars(*f);

  if(f->indent>0 && f->begin < f->end && f->end[-1]=='\n' && text[0]!='\n')
  {
    const usize spaces_per_tab = 2;
    const usize num_spaces = spaces_per_tab * f->indent;
    assert_usize_lte(num_spaces, avail);
    
    memset(f->end, ' ', num_spaces);
    avail -= num_spaces;
    f->end += num_spaces;
  }

  va_list args;
  va_start(args, text);
  ssize bytes_written = vsnprintf(f->end, avail, text, args);
  va_end(args);
  assert_ssize_lte(0, bytes_written); // runtime error
  assert_usize_lt(bytes_written, avail); // out of memory

  f->end += bytes_written;
}

