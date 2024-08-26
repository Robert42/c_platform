// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "mem.h"

void _swap_scratch(Mem_Region scratch_1, Mem_Region scratch_2)
{
  if(SCRATCH.end == scratch_1.end)
  {
    debug_assert_ptr_lte_lte(scratch_1.begin, SCRATCH.begin, scratch_1.end);
    SCRATCH = scratch_2;
  }
  else
  {
    debug_assert_ptr_eq(SCRATCH.end, scratch_2.end);
    debug_assert_ptr_lte_lte(scratch_2.begin, SCRATCH.begin, scratch_2.end);
    SCRATCH = scratch_1;
  }
}

Mem_Region _mem_region_from(void* begin, usize len)
{
  return (Mem_Region){
    .begin = begin,
    .end = begin+len,
  };
}

void* mem_region_alloc_bytes_unaligned(Mem_Region* region, usize num_bytes)
{
  void* bytes = region->begin;
  region->begin += num_bytes;
  debug_assert_ptr_lte(region->begin, region->end);
  return bytes;
}
