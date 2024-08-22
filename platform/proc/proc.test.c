// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "proc.h"

struct S { bool x, y; };
void proc_test()
{
  uint8_t BUFFER[512];
  Mem_Region region = MEM_REGION_FROM_ARRAY(BUFFER);
  const struct Proc_Exec_Blocking_Settings capture_stdout = {.capture_stdout=true, .region_stdout=&region};
  const struct Proc_Exec_Blocking_Settings capture_stderr = {.capture_stderr=true, .region_stderr=&region};

  // TODO: Create own programs to test instead!
  // these tests are fragile. They only work on linux and may change when the software gets updated!

  {
    char msg[] = "Hello, World!";
    char* const args[] = {"echo", "-n", msg, NULL};
    struct Proc_Exec_Blocking_Result result = proc_exec_blocking(args, capture_stdout);

    assert_cstr_eq(result.captured_stdout, msg);
    debug_assert_ptr_eq(region.begin, BUFFER + ARRAY_LEN(msg));
  }

  {
    region.begin = BUFFER;
    char* const args[] = {"tcc", "/NOT_EXISTING", NULL};
    struct Proc_Exec_Blocking_Result result = proc_exec_blocking(args, capture_stderr);

    const char* expected = "tcc: error: file '/NOT_EXISTING' not found\n";
    assert_cstr_eq(result.captured_stderr, expected);
    debug_assert_ptr_eq(region.begin, BUFFER + strlen(expected)+1);
  }

  // assert when buffer way too small
  EXPECT_ASSERT(
  {
    uint8_t BUFFER[4];
    Mem_Region region = MEM_REGION_FROM_ARRAY(BUFFER);

    char* const args[] = {"echo", "-n", "more than four bytes", NULL};
    const struct Proc_Exec_Blocking_Settings too_small_buffer = {.capture_stdout=true, .region_stdout=&region};
    proc_exec_blocking(args, too_small_buffer);
  }
  );
}