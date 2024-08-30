// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#define ARRAY_LEN(XS) (sizeof (XS) / sizeof (XS)[0])

// ==== mempry regions ====

typedef struct _platform_mem_Region
{
  unsigned char* begin;
  unsigned char* end;
} Mem_Region;
/*@
predicate valid_region{L}(Mem_Region region) =
  \valid(region.begin) &&
  \offset(region.end) <= \block_length(region.end) &&
  \base_addr{L}(region.begin) == \base_addr{L}(region.end) &&
  region.begin <= region.end;
*/

extern Mem_Region SCRATCH;

void _mem_swap_scratch(Mem_Region* scratch_var, Mem_Region region_1, Mem_Region region_2);

Mem_Region _mem_region_from(void* begin, usize len);
#define MEM_REGION_FROM_ARRAY(XS) _mem_region_from(XS, sizeof XS)

/*@ requires \valid(r) && valid_region(*r);
*/
static inline usize mem_region_available_bytes(const Mem_Region* r){return r->end - r->begin;}

void* mem_region_alloc_bytes_unaligned(Mem_Region* region, usize num_bytes);
