// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

typedef struct _utils_Fmt
{
  char* begin; // also the beginning of the buffer
  usize buffer_capacity;
  char* end;
} Fmt;

/*@ predicate fmt_valid(Fmt f) =
  \valid(f.begin + (0 .. f.buffer_capacity-1))
  && \offset(f.begin)+f.buffer_capacity <= \block_length(f.begin)
  && f.begin <= f.end < f.begin+f.buffer_capacity
  && f.buffer_capacity > 0
  && f.end[0] == 0 // So f.begin is always a valid nullterminated cstr
;
*/

Fmt fmt_new(char* buffer, usize capacity);
void fmt(Fmt* f, const char* text, ...);
