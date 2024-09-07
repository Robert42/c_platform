// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "io/path.test.c"
#include "proc/proc.test.c"
#include "time/timer.test.c"

void platform_test()
{
  path_test();
  proc_test();
  timer_test();
}
