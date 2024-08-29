// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#define ARRAY_LEN(XS) (sizeof (XS) / sizeof (XS)[0])

// ==== mempry regions ====

typedef struct
{
  unsigned char* begin;
  unsigned char* end;
} Mem_Region;

extern Mem_Region SCRATCH;
void _mem_swap_scratch(Mem_Region scratch_1, Mem_Region scratch_2);

Mem_Region _mem_region_from(void* begin, usize len);
#define MEM_REGION_FROM_ARRAY(XS) _mem_region_from(XS, sizeof XS)

static inline usize mem_region_available_bytes(const Mem_Region* r){return r->end - r->begin;}

void* mem_region_alloc_bytes_unaligned(Mem_Region* region, usize num_bytes);
