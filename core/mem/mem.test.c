// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "mem.h"

void mem_test()
{
  // size constants
  {
    assert_usize_eq(KiB, ((usize)1) << 10);
    assert_usize_eq(MiB, ((usize)1) << 20);
    assert_usize_eq(GiB, ((usize)1) << 30);
    assert_usize_eq(TiB, ((usize)1) << 40);
    assert_usize_eq(1024, KiB);
    assert_usize_eq(1024, ((usize)1) << 10);
    assert_usize_eq(1024*KiB, MiB);
    assert_usize_eq(MiB, ((usize)1) << 20);
    assert_usize_eq(1024*KiB, ((usize)1) << 20);
    assert_usize_eq(1024*MiB, GiB);
    assert_usize_eq(2*GiB, ((usize)2) << 30);
#if ENV_PTR_BITS >= 64
    assert_usize_eq(8*GiB, ((usize)8) << 30);
    assert_usize_eq(2*TiB, ((usize)2) << 40);
#endif
  }

  {
#define LEN 20
  u8 abc[LEN];
  assert_usize_eq(ARRAY_LEN(abc), LEN);
  
  Mem_Region region = MEM_REGION_FROM_ARRAY(abc);
  assert_ptr_eq(region.begin, &abc[0]);
  assert_ptr_eq(region.end, &abc[LEN]);
  assert_usize_eq(mem_region_available_bytes(region), LEN);
#undef LEN

  void* bytes_1 = mem_region_alloc_bytes_unaligned(&region, 4);
  assert_ptr_eq(bytes_1, &abc[0]);
  void* bytes_2 = mem_region_alloc_bytes_unaligned(&region, 8);
  assert_ptr_eq(bytes_2, &abc[4]);
  void* bytes_3 = mem_region_alloc_bytes_unaligned(&region, 8);
  assert_ptr_eq(bytes_3, &abc[12]);

  EXPECT_DEBUG_ASSERT(
  mem_region_alloc_bytes_unaligned(&region, 4);
  );
  }

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

  // alignof macro
  {
    assert_usize_eq(sizeof(int), alignof(int));
  }

  // align region
  {
    u8 BUFFER[256];
    Mem_Region region = MEM_REGION_FROM_ARRAY(BUFFER);

    mem_region_align(&region, 8);
    assert_usize_eq((usize)region.begin % 8, 0);

    mem_region_alloc_bytes_unaligned(&region, 1);
    assert_usize_eq((usize)region.begin % 8, 1);

    mem_region_alloc_bytes_unaligned(&region, 5);
    assert_usize_eq((usize)region.begin % 8, 6);

    mem_region_align(&region, 8);
    assert_usize_eq((usize)region.begin % 8, 0);
  }

  // `mem_region_copy_to_region`
  {
    u8 BUFFER[256] = {0};
    Mem_Region region = MEM_REGION_FROM_ARRAY(BUFFER);

    mem_region_align(&region, alignof(int));
    mem_region_alloc_bytes_unaligned(&region, 1);
    assert_usize_eq((usize)region.begin % alignof(int), 1);

    void* const expected_ptr = region.begin + alignof(int) - 1;

    int xs[3] = {42, 37, 137};
    int* ys = MEM_REGION_COPY_ARRAY(&region, int, xs, ARRAY_LEN(xs));
    assert_ptr_eq(ys, expected_ptr);
    assert_ptr_eq(region.begin, ys + 3);

    assert_int_eq(ys[0], 42);
    assert_int_eq(ys[1], 37);
    assert_int_eq(ys[2], 137);
  }
}
