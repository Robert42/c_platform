// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "platform/prelude.h"

#include "platform/platform.c"
#include "utils/utils.c"

Mem_Region SCRATCH = {};

static u8 _SCRATCH_BUFFER_1[1024*1024] = {};
static u8 _SCRATCH_BUFFER_2[ARRAY_LEN(_SCRATCH_BUFFER_1)] = {};
void scratch_swap()
{
  _mem_swap_scratch(MEM_REGION_FROM_ARRAY(_SCRATCH_BUFFER_1), MEM_REGION_FROM_ARRAY(_SCRATCH_BUFFER_2));
}

void c_script_init()
{
  platform_init();

  SCRATCH = MEM_REGION_FROM_ARRAY(_SCRATCH_BUFFER_1);
}
