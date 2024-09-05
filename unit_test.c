// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "platform/platform.c"
#include "utils/utils.c"

#include "platform/test.c"
#include "utils/test.c"

static u8 _SCRATCH_BUFFER_1[1024*1024] = {0};
Mem_Region SCRATCH = {0};

int main(int argc, const char** argv)
{
  platform_init();

  SCRATCH = MEM_REGION_FROM_ARRAY(_SCRATCH_BUFFER_1);

#if 0
  term_demo();
  dev_env_demo();
#endif

  platform_test();
  utils_test();

  printf("%s==== DONE ====%s\n", TERM.green_bold, TERM.normal);

  return EXIT_SUCCESS;
}
