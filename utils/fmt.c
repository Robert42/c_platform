// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "fmt.h"

/*@ requires valid_buffer: \valid(buffer + (0 .. capacity-1));
    requires \offset(buffer)+capacity <= \block_length(buffer);
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

  return f;
}
