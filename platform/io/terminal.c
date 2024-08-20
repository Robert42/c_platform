// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "terminal.h"

const char* TERM_RED = "";
const char* TERM_GREEN = "";
const char* TERM_RED_BOLD = "";
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
#define RED_FG "31"
#define GREEN_FG "32"
    TERM_RED = "\e[" NORMAL ";" RED_FG "m";
    TERM_RED_BOLD = "\e[" BOLD ";" RED_FG "m";
    TERM_GREEN = "\e[" NORMAL ";" GREEN_FG "m";
    TERM_GREEN_BOLD = "\e[" BOLD ";" GREEN_FG "m";
    TERM_NORMAL = "\e[" NORMAL "m";
#undef BOLD
#undef NORMAL
#undef RED_FG
#undef GREEN_FG
  }
}

void term_demo()
{
  printf("%s-- red --\n", TERM_RED);
  printf("%s-- red bold --\n", TERM_RED_BOLD);
  printf("%s-- green --\n", TERM_GREEN);
  printf("%s-- green bold --\n", TERM_GREEN_BOLD);
  printf("%s-- normal --\n", TERM_NORMAL);
}
