// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "proc.h"

struct S { bool x, y; };
void proc_test()
{
  uint8_t BUFFER[16];
  Mem_Region region = MEM_REGION_FROM_ARRAY(BUFFER);
  const struct Proc_Exec_Blocking_Settings capture_stdout = {.capture_stdout=true, .region_stdout=&region};

  {
    char msg[] = "Hello, World!";
    char* const args[] = {"echo", "-n", msg, NULL};
    struct Proc_Exec_Blocking_Result result = proc_exec_blocking(args, capture_stdout);

    debug_assert_ptr_eq(region.begin, BUFFER + ARRAY_LEN(msg));

    printf("CAPTURED: `%s`\n", result.captured_stdout);
  }
}
