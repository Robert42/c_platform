// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "mem.h"

/*@ requires \valid(scratch_var) && valid_region(*scratch_var);
    requires valid_region(region_1);
    requires valid_region(region_2);
    ensures valid_region(*scratch_var);
*/
void _mem_swap_scratch(Mem_Region* scratch_var, Mem_Region region_1, Mem_Region region_2)
{
  if(scratch_var->end == region_1.end)
  {
    debug_assert_ptr_lte_lte(region_1.begin, scratch_var->begin, region_1.end);
    *scratch_var = region_2;
  }
  else
  {
    debug_assert_ptr_eq(scratch_var->end, region_2.end);
    debug_assert_ptr_lte_lte(region_2.begin, scratch_var->begin, region_2.end);
    *scratch_var = region_1;
  }
}

/*@ requires \valid((char*)begin) && \offset((char*)begin)+len <= \block_length((char*)begin);
    ensures valid_region(\result);
*/
Mem_Region _mem_region_from(void* begin, usize len)
{
  return (Mem_Region){
    .begin = begin,
    .end = (unsigned char*)begin+len,
  };
}

/*@ requires \valid(region) && valid_region(*region);
    ensures valid_region(*region);
*/
void* mem_region_alloc_bytes_unaligned(Mem_Region* region, usize num_bytes)
{
  void* bytes = region->begin;
  region->begin += num_bytes;
  /* TODO: my owna ssert function should be sufficient
  assert_ptr_lte(region->begin, region->end);
  */
  if(region->begin >= region->end)
    abort();
  return bytes;
}
