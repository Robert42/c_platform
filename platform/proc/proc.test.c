// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "proc.h"

struct S { bool x, y; };
void proc_test()
{
  const struct Proc_Exec_Blocking_Settings capture_stdout = {.capture_stdout=true};

  {
    const char* const args[] = {"echo", "Hello, World!", NULL};
    struct Proc_Exec_Blocking_Result result = proc_exec_blocking(args, capture_stdout);
  }
}
