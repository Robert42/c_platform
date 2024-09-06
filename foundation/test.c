// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "dev/assert.test.c"
#include "mem/mem.test.c"
#include "ty/str.test.c"
#include "fmt.test.c"

void foundation_test()
{
  assert_test();
  mem_test();
  str_test();
  fmt_test();
}
