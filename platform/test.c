// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "io/path.test.c"
#include "proc/proc.test.c"
#include "time/timer.test.c"
#include "mem/mem_page.test.c"
#include "mem/mem_huge_array.test.c"

void platform_test()
{
  mem_page_test();
  mem_huge_array_test();
  path_test();
  proc_test();
  timer_test();
}
