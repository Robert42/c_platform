// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "platform/system_header.h"
#include "platform/mem/mem.h"

#include "platform/platform.c"
#include "platform/io/terminal.c"
#include "platform/mem/mem.c"

Mem_Region SCRATCH = {};

static uint8_t _SCRATCH_BUFFER_1[1024*1024] = {};

void c_script_init()
{
  platform_init();

  SCRATCH = MEM_REGION_FROM_ARRAY(_SCRATCH_BUFFER_1);
}
