// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "dev/assert.test.c"
#include "math/round.test.c"
#include "mem/mem.test.c"
#include "ty/char.test.c"
#include "ty/str.test.c"
#include "ty/cstr.test.c"
#include "fmt.test.c"

void core_test()
{
  assert_test();
  mem_test();
  math_round_test();
  char_test();
  cstr_test();
  str_test();
  fmt_test();
}
