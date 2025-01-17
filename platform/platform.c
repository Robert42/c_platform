// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "prelude.h"

#include "io/file.h"
#include "proc/proc.h"

void term_init(void);
void timer_init(void);

Mem_Region PANIC_REGION;
static u8 PANIC_BUFFER[16*1024];

void platform_init()
{
  PANIC_REGION = MEM_REGION_FROM_ARRAY(PANIC_BUFFER);

  term_init();
  timer_init();
  mem_page_init();
}

#include "dev/diff.c"
#include "io/terminal.c"
#include "io/env.c"
#include "io/path.c"
#include "io/file.c"
#include "time/timer.c"
#include "mem/mem_page.c"
#include "mem/mem_huge_array.c"

#ifdef __linux__
#include "io/file.linux.c"
#include "proc/proc.linux.c" // depends on "io/file.linux.c"
#include "time/timer.linux.c"
#include "mem/mem_page.linux.c"
#endif

