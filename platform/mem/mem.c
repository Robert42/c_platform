// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "mem.h"

/*@ predicate mem_region_separated(Mem_Region a, Mem_Region b) = \separated(a.full_range_begin + (0 .. a.full_range_len), b.full_range_begin + (0 .. b.full_range_len));
*/

/*@ requires valid_ptr: \valid(scratch_var);
    requires valid_ptr_region: mem_region_valid(*scratch_var);
    requires valid_region_1: mem_region_valid(region_1);
    requires valid_region_2: mem_region_valid(region_2);
    requires separate_regions: mem_region_separated(region_1, region_2);
    requires var_not_sep: !mem_region_separated(region_1, *scratch_var) || !mem_region_separated(region_2, *scratch_var);
    requires var_identical_end: region_1.end == scratch_var->end || region_2.end == scratch_var->end;
    assigns \nothing;
    ensures mem_region_valid(*scratch_var);
    ensures mem_region_separated(region_1, \old(*scratch_var)) ==> !mem_region_separated(region_2, *scratch_var);
    ensures mem_region_separated(region_2, \old(*scratch_var)) ==> !mem_region_separated(region_1, *scratch_var);
*/
void _mem_swap_scratch(Mem_Region* scratch_var, Mem_Region region_1, Mem_Region region_2)
{
  if((usize)scratch_var->end == (usize)region_1.end)
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

/*@ requires ValidBuffer: \valid(begin + (0 .. len-1)) && \offset(begin)+len <= \block_length(begin);
    requires NotTooLargeBuffer: (ssize)len == (usize)len;
    assigns \nothing;
    ensures ValidRegion: mem_region_valid(\result);
*/
Mem_Region _mem_region_from(unsigned char* begin, usize len)
{
  Mem_Region region = {
    .begin = begin,
    .end = begin+len,
#if GHOST
    .full_range_begin = begin,
    .full_range_len = len,
    .bytes_available = len,
#endif
  };
  return region;
}

/*@ requires \valid(region) && mem_region_valid(*region);
    assigns *region;
    assigns \result \from region->begin;
    ensures region_still_valid: mem_region_valid(*region);
    ensures returned_valid: \valid(\result + (0 .. num_bytes-1));
    ensures separated: \separated(\result + (0 .. num_bytes-1), region->begin + (0.. region->bytes_available));
    ensures part_of_full_region: region->full_range_begin <= \result <= \result+num_bytes == region->begin <= region->full_range_begin+region->full_range_len;
*/
unsigned char* mem_region_alloc_bytes_unaligned(Mem_Region* region, usize num_bytes)
{
  assert_usize_lte(num_bytes, mem_region_available_bytes(*region));

  unsigned char* const bytes = region->begin;

  region->begin += num_bytes;
#if GHOST
  region->bytes_available -= num_bytes;
#endif

  return bytes;
}
