// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "mem.h"

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
