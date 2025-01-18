// Copyright (c) 2024-2025 Robert Hildebrandt. All rights reserved.
#include "proc.h"

struct S { bool x, y; };
void proc_test()
{
  u8 BUFFER[512];
  Mem_Region region = MEM_REGION_FROM_ARRAY(BUFFER);
  const struct Proc_Exec_Blocking_Settings capture_stdout = {.capture_stdout=true, .region_stdout=&region};
  const struct Proc_Exec_Blocking_Settings capture_stderr = {.capture_stderr=true, .region_stderr=&region};

  for(usize i=0; i<sizeof(BUFFER); ++i) BUFFER[i] = 0xCC;

  // If I ever run these tests outside linux, it may be a good idea to create
  // own programs to test instead of using linux commands.
  // Alternatively start different processes depending on the OS

  {
    char msg[] = "Hello, World!";
    char* const args[] = {"echo", "-n", msg, NULL};
    struct Proc_Exec_Blocking_Result result = proc_exec_blocking(args, capture_stdout);

    assert_cstr_eq(result.captured_stdout, msg);
    assert_int_eq(result.exit_code, EXIT_SUCCESS);
    assert(result.exit_normal);
    assert(result.success);
    debug_assert_ptr_eq(region.begin, BUFFER + ARRAY_LEN(msg));
  }

  {
    region.begin = BUFFER;
    for(usize i=0; i<sizeof(BUFFER); ++i) BUFFER[i] = 0xCC;
    char* const args[] = {"ls", "--totally_normal_option", NULL};
    struct Proc_Exec_Blocking_Result result = proc_exec_blocking(args, capture_stderr);

    const char* expected = "ls: unrecognized option '--totally_normal_option'\nTry 'ls --help' for more information.\n";
    assert_cstr_eq(result.captured_stderr, expected);
    debug_assert_ptr_eq(region.begin, BUFFER + strlen(expected)+1);
    assert_int_ne(result.exit_code, EXIT_SUCCESS);
    assert(result.exit_normal);
    assert(!result.success);
  }

  // assert when buffer way too small
  EXPECT_ASSERT(
  {
    u8 BUFFER[5];
    Mem_Region region = _mem_region_from(BUFFER, 4); // Let's pretend, the buffer was only four bytes large.

    char* const args[] = {"echo", "-n", "more than four bytes", NULL};
    const struct Proc_Exec_Blocking_Settings too_small_buffer = {.capture_stdout=true, .region_stdout=&region};
    proc_exec_blocking(args, too_small_buffer);
  }
  );
}
