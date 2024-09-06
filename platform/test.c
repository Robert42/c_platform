// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "mem/mem.test.c"
#include "proc/proc.test.c"
#include "time/timer.test.c"

void platform_test()
{
  mem_test();
  proc_test();
  timer_test();
}
