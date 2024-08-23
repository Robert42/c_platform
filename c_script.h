// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "platform/system_header.h"
#include "platform/mem/mem.h"
#include "platform/dev/dev.h"

#include "platform/platform.c"
#include "platform/io/terminal.c"
#include "platform/mem/mem.c"
#include "platform/dev/dev.c"
#include "utils/path.c"
#ifdef __linux__
#include "platform/io/file.linux.c"
#include "platform/proc/proc.linux.c"
#endif

Mem_Region SCRATCH = {};

static u8 _SCRATCH_BUFFER_1[1024*1024] = {};

void c_script_init()
{
  platform_init();

  SCRATCH = MEM_REGION_FROM_ARRAY(_SCRATCH_BUFFER_1);
}
