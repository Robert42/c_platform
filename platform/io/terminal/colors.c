// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "colors.h"

void platform_io_terminal_colors_init()
{
#ifdef __linux__
  bool is_terminal = isatty(STDOUT_FILENO) == 1;
#else
#error unimplemented
#endif
  

  if(is_terminal)
    printf("TTY!\n");
  else
    printf(":(\n");
}
