// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "c_script.h"

#include "platform/test.c"
#include "utils/test.c"

int main(int argc, const char** argv)
{
  c_script_init();

  term_demo();
  dev_env_demo();

  platform_test();
  utils_test();

  printf("%s==== DONE ====%s\n", TERM_GREEN_BOLD, TERM_NORMAL);
  return 0;
}
