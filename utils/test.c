// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "path.test.c"
#include "str.test.c"
#include "fmt.test.c"
#include "collections/set/setintcddo.test.c"

void utils_test()
{
  path_test();
  str_test();
  fmt_test();
  setintcddo_test();
}
