// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "prelude.h"

void term_init();

void platform_init()
{
  term_init();
}

#include "io/terminal.c"
#include "mem/mem.c"
#include "dev/dev.c"

#ifdef __linux__
#include "io/file.linux.c"
#include "proc/proc.linux.c" // depends on "io/file.linux.c"
#endif
