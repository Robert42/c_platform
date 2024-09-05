// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "str.h"

void str_test()
{
  // str_from_cstr_slice
  {
    const char src[] = "Let me say: Hello, World";
    const str s = str_from_cstr_len(src+12, 5);

    assert_ptr_eq(s.begin, src+12);
    assert_ptr_eq(s.end, src+12+5);
    assert_usize_eq(str_len(s), 5);
    
    const str empty = str_from_cstr_len(src+3, 0);
    assert_ptr_eq(empty.begin, src+3);
    assert_ptr_eq(empty.end, empty.begin);
    assert_usize_eq(str_len(empty), 0);
  }
  
  // cstr_fmt
  {
    u8 BUFFER[4096];
    Mem_Region region = MEM_REGION_FROM_ARRAY(BUFFER);
    
    assert_cstr_eq(cstr_fmt(&region, "Hello, %s!", "World"), "Hello, World!");
  }
}
