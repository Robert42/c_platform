// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "mem.h"

void mem_test()
{
#define LEN 5
  uint32_t abc[LEN];
  if(ARRAY_LEN(abc) != LEN) abort();
  
  Mem_Region region = MEM_REGION_FROM_ARRAY(abc);
  if(region.begin != &abc[0]) abort();
  if(region.end != &abc[LEN]) abort();
#undef LEN
}
