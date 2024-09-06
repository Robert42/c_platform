// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#define ARRAY_LEN(XS) (sizeof (XS) / sizeof (XS)[0])

// ==== mempry regions ====

struct _platform_mem_Region;
typedef struct _platform_mem_Region Mem_Region;
struct _platform_mem_Region
{
  unsigned char* begin;
  unsigned char* end;

#if GHOST
  unsigned char* full_range_begin;
  usize full_range_len;

  ssize bytes_available;
#endif
};

/*@ predicate mem_region_valid(Mem_Region region) =
  \valid(region.full_range_begin + (0 .. region.full_range_len-1))
  && \offset(region.full_range_begin)+region.full_range_len <= \block_length(region.full_range_begin)
  && region.full_range_begin <= region.begin <= region.end == region.full_range_begin+region.full_range_len
  && region.begin + region.bytes_available == region.end
  && region.bytes_available >= 0
;
*/

extern Mem_Region SCRATCH;
extern Mem_Region STACK;
extern Mem_Region PANIC_REGION;

void _mem_swap_scratch(Mem_Region* scratch_var, Mem_Region region_1, Mem_Region region_2);

Mem_Region _mem_region_from(unsigned char* begin, usize len);
#define MEM_REGION_FROM_ARRAY(XS) _mem_region_from(XS, sizeof XS)

/*@ requires mem_region_valid(r);
    assigns \nothing;
    ensures \result == r.bytes_available;
*/
static inline usize mem_region_available_bytes(const Mem_Region r)
{
  const ssize diff = r.end - r.begin;
  //@ assert CorrectDiff: r.bytes_available == diff;
  //@ assert NonNegative: r.bytes_available >= 0;
  return diff;
}

unsigned char* mem_region_alloc_bytes_unaligned(Mem_Region* region, usize num_bytes);
