// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "codegen/gen_table.test.c"
#include "collections/set/setintcddo.test.c"

void utils_test()
{
  gen_adt_test();
  setintcddo_test();
}
