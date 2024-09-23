// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "core/prelude.h"
#include "platform/prelude.h"

#include "core/core.c"
#include "platform/platform.c"
#include "utils/utils.c"
#include "c_compiler/c_compiler.c"

Mem_Region SCRATCH = {0};

Mem_Region SCRATCH_1 = {0};
Mem_Region SCRATCH_2 = {0};
void scratch_swap()
{
  _mem_swap_scratch(&SCRATCH, SCRATCH_1, SCRATCH_2);
}

Mem_Region STACK = {0};

Mem_Region PERSISTENT = {0};

void c_script_init()
{
  platform_init();

  SCRATCH_1 = mem_region_from_pre_reserved(1*MiB);
  SCRATCH_2 = mem_region_from_pre_reserved(1*MiB);
  SCRATCH = SCRATCH_1;

  STACK = mem_region_from_pre_reserved(1*MiB);
  PERSISTENT = mem_region_from_pre_reserved(1*MiB);

  cc_init();
}
