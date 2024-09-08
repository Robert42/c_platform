// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "core/prelude.h"
#include "platform/prelude.h"

#include "core/core.c"
#include "platform/platform.c"
#include "utils/utils.c"
#include "c_compiler/c_compiler.c"

Mem_Region SCRATCH = {0};

static u8 _SCRATCH_BUFFER_1[1024*1024] = {0};
static u8 _SCRATCH_BUFFER_2[ARRAY_LEN(_SCRATCH_BUFFER_1)] = {0};
void scratch_swap()
{
  _mem_swap_scratch(&SCRATCH, MEM_REGION_FROM_ARRAY(_SCRATCH_BUFFER_1), MEM_REGION_FROM_ARRAY(_SCRATCH_BUFFER_2));
}

Mem_Region STACK = {0};
static u8 _STACK_BUFFER[1024*1024] = {0};

static u8 _PERSISTENT_BUFFER[1024*1024] = {0};
Mem_Region PERSISTENT = {0};

void c_script_init()
{
  platform_init();

  SCRATCH = MEM_REGION_FROM_ARRAY(_SCRATCH_BUFFER_1);
  STACK = MEM_REGION_FROM_ARRAY(_STACK_BUFFER);
  PERSISTENT = MEM_REGION_FROM_ARRAY(_PERSISTENT_BUFFER);

  cc_init();
}
