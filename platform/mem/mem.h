// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#define ARRAY_LEN(XS) (sizeof (XS) / sizeof (XS)[0])

// ==== mempry regions ====

typedef struct
{
  void* begin;
  void* end;
} Mem_Region;

extern Mem_Region SCRATCH;

Mem_Region _mem_region_from(void* begin, ssize_t len);
#define MEM_REGION_FROM_ARRAY(XS) _mem_region_from(XS, sizeof XS)

