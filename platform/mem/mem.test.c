// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "mem.h"

void mem_test()
{
  uint32_t abc[5];
  if(ARRAY_LEN(abc) != 5) abort();
}
