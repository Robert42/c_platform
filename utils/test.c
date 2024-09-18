// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "codegen/gen_adt.test.c"
#include "collections/set/setintcddo.test.c"

void utils_test()
{
  gen_adt_test();
  setintcddo_test();
}
