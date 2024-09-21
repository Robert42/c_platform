// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

const char* const BANNER = "// <BANNER>\n";

#include "codegen/gen_table.c"
#include "codegen/gen_table.test.c"
#include "collections/set/setintcddo.test.c"

void utils_test()
{
  gen_table_test();
  setintcddo_test();
}
