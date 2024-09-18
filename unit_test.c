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

static u8 _SCRATCH_BUFFER_1[1024*1024] = {0};
static u8 _STACK_BUFFER[256*1024*1024] = {0};
Mem_Region SCRATCH = {0};
Mem_Region STACK = {0};

int main(UNUSED int argc, UNUSED const char** argv)
{
  platform_init();
  ui_init();

  SCRATCH = MEM_REGION_FROM_ARRAY(_SCRATCH_BUFFER_1);
  STACK = MEM_REGION_FROM_ARRAY(_STACK_BUFFER);

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
