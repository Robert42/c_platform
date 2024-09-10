// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

typedef struct _utils_Fmt
{
  char* begin; // also the beginning of the buffer
  usize buffer_capacity;
  char* end;

  usize indent;
} Fmt;

Fmt fmt_new(char* buffer, usize capacity);
Fmt fmt_new_from_region(Mem_Region* region, usize capacity);
void fmt_write(Fmt* f, const char* text, ...) ATT_PRINTF(2, 3);

