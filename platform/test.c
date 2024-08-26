// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "dev/dev.test.c"
#include "mem/mem.test.c"
#include "proc/proc.test.c"
#include "time/timer.test.c"

void platform_test()
{
  dev_test();
  mem_test();
  proc_test();
  timer_test();
}
