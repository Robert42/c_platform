// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

const char* const BANNER = "// <BANNER>\n";

#include "collections/set/setintcddo.test.c"
#include "parser/c_tok.test.c"
#include "parser/ini.test.c"

void utils_test()
{
  setintcddo_test();
  c_tok_test();
  ini_test();
}
