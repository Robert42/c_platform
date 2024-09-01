// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "mem.h"

void mem_test()
{
#define LEN 5
  u8 abc[LEN];
  assert_usize_eq(ARRAY_LEN(abc), LEN);
  
  Mem_Region region = MEM_REGION_FROM_ARRAY(abc);
  assert_ptr_eq(region.begin, &abc[0]);
  assert_ptr_eq(region.end, &abc[LEN]);
#undef LEN

  void* bytes_1 = mem_region_alloc_bytes_unaligned(&region, 4);
  assert_ptr_eq(bytes_1, &abc[0]);
  void* bytes_2 = mem_region_alloc_bytes_unaligned(&region, 8);
  assert_ptr_eq(bytes_2, &abc[1]);
  void* bytes_3 = mem_region_alloc_bytes_unaligned(&region, 8);
  assert_ptr_eq(bytes_3, &abc[3]);

  EXPECT_DEBUG_ASSERT(
  mem_region_alloc_bytes_unaligned(&region, 4);
  );

  // swap scratch
  {
    u8 TEST_SCRATCH_1[256];
    u8 TEST_SCRATCH_2[128];

    Mem_Region scratch = MEM_REGION_FROM_ARRAY(TEST_SCRATCH_1);
    assert_ptr_eq(scratch.begin, TEST_SCRATCH_1);
    assert_ptr_eq(scratch.end, TEST_SCRATCH_1 + ARRAY_LEN(TEST_SCRATCH_1));

    mem_region_alloc_bytes_unaligned(&scratch, 3);
    assert_ptr_eq(scratch.begin, TEST_SCRATCH_1+3);
    assert_ptr_eq(scratch.end, TEST_SCRATCH_1 + ARRAY_LEN(TEST_SCRATCH_1));

    _mem_swap_scratch(&scratch, MEM_REGION_FROM_ARRAY(TEST_SCRATCH_1), MEM_REGION_FROM_ARRAY(TEST_SCRATCH_2));
    assert_ptr_eq(scratch.begin, TEST_SCRATCH_2);
    assert_ptr_eq(scratch.end, TEST_SCRATCH_2 + ARRAY_LEN(TEST_SCRATCH_2));

    _mem_swap_scratch(&scratch, MEM_REGION_FROM_ARRAY(TEST_SCRATCH_1), MEM_REGION_FROM_ARRAY(TEST_SCRATCH_2));
    assert_ptr_eq(scratch.begin, TEST_SCRATCH_1);
    assert_ptr_eq(scratch.end, TEST_SCRATCH_1 + ARRAY_LEN(TEST_SCRATCH_1));
  }
}
