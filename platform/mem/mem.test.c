// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "mem.h"

void mem_test()
{
#define LEN 5
  uint32_t abc[LEN];
  assert_usize_eq(ARRAY_LEN(abc), LEN);
  
  Mem_Region region = MEM_REGION_FROM_ARRAY(abc);
  assert_ptr_eq(region.begin, &abc[0]);
  assert_ptr_eq(region.end, &abc[LEN]);
#undef LEN
}
