#!/usr/bin/env -S tcc -run
// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "c_script.h"

int main(int argc, const char** argv)
{
  c_script_init();

  term_demo();

  printf("%s==== DONE ====%s\n", TERM_GREEN_BOLD, TERM_NORMAL);
  return 0;
}
