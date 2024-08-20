// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "terminal.h"

const char* TERM_GREEN_BOLD = "";
const char* TERM_NORMAL = "";

void term_init()
{
#ifdef __linux__
  bool is_terminal = isatty(STDOUT_FILENO) == 1;
#else
#error unimplemented
#endif
  
  if(is_terminal)
  {
#define NORMAL "0"
#define BOLD "1"
#define GREEN_FG "32"
    TERM_GREEN_BOLD = "\e[" BOLD ";" GREEN_FG "m";
    TERM_NORMAL = "\e[" NORMAL "m";
#undef BOLD
#undef NORMAL
#undef GREEN_FG
  }
}

void term_demo()
{
  printf("%s-- green bold --\n", TERM_GREEN_BOLD);
  printf("%s-- normal --\n", TERM_NORMAL);
}
