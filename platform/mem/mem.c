// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "mem.h"

Mem_Region _mem_region_from(void* begin, ssize_t len)
{
  return (Mem_Region){
    .begin = begin,
    .end = begin+len,
  };
}

