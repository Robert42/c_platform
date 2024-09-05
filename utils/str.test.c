// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "str.h"

void str_test()
{
  u8 BUFFER[4096];
  Mem_Region region = MEM_REGION_FROM_ARRAY(BUFFER);
  
  assert_cstr_eq(cstr_fmt(&region, "Hello, %s!", "World"), "Hello, World!");
}
