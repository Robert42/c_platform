// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "platform/system_header.h"

#include "platform/platform.c"
#include "platform/io/terminal/colors.c"

void c_script_init()
{
  platform_init();
}
