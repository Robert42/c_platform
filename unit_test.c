// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "core/core.c"
#include "platform/platform.c"
#include "utils/utils.c"
#include "ui/ui.c"

#include "core/test.c"
#include "platform/test.c"
#include "utils/test.c"
#include "ui/test.c"

#define PRINT_ENV 0

#if PRINT_ENV
#include "core/env.demo.c"
#endif

Mem_Region SCRATCH = {0};
Mem_Region STACK = {0};

int main(UNUSED int argc, UNUSED const char** argv)
{
  platform_init();
  ui_init();

  SCRATCH = mem_region_from_pre_reserved(1*MiB);
  STACK = mem_region_from_pre_reserved(1*GiB);

#if 0
  term_demo();
#endif
#if PRINT_ENV
  dev_env_demo();
#endif

  core_test();
  platform_test();
  utils_test();
  ui_test();

  printf("%s==== DONE ====%s\n", TERM.green_bold, TERM.normal);

  return EXIT_SUCCESS;
}
