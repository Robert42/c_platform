// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "terminal.h"

const char* TERM_RED = "";
const char* TERM_RED_BOLD = "";
const char* TERM_GREEN = "";
const char* TERM_GREEN_BOLD = "";
const char* TERM_YELLOW = "";
const char* TERM_YELLOW_BOLD = "";
const char* TERM_BLUE = "";
const char* TERM_BLUE_BOLD = "";

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
#define YELLOW_FG "33"
#define BLUE_FG "34"
    TERM_RED = "\e[" NORMAL ";" RED_FG "m";
    TERM_RED_BOLD = "\e[" BOLD ";" RED_FG "m";
    TERM_GREEN = "\e[" NORMAL ";" GREEN_FG "m";
    TERM_GREEN_BOLD = "\e[" BOLD ";" GREEN_FG "m";
    TERM_YELLOW = "\e[" NORMAL ";" YELLOW_FG "m";
    TERM_YELLOW_BOLD = "\e[" BOLD ";" YELLOW_FG "m";
    TERM_BLUE = "\e[" NORMAL ";" BLUE_FG "m";
    TERM_BLUE_BOLD = "\e[" BOLD ";" BLUE_FG "m";
    TERM_NORMAL = "\e[" NORMAL "m";
#undef BOLD
#undef NORMAL
#undef RED_FG
#undef GREEN_FG
#undef YELLOW_FG
#undef BLUE_FG
  }
}

void term_demo()
{
  printf("%s-- red normal --\n", TERM_RED);
  printf("%s-- red bold --\n", TERM_RED_BOLD);
  printf("%s-- green normal --\n", TERM_GREEN);
  printf("%s-- green bold --\n", TERM_GREEN_BOLD);
  printf("%s-- yellow normal --\n", TERM_YELLOW);
  printf("%s-- yellow bold --\n", TERM_YELLOW_BOLD);
  printf("%s-- blue normal --\n", TERM_BLUE);
  printf("%s-- blue bold --\n", TERM_BLUE_BOLD);
  printf("%s-- normal --\n", TERM_NORMAL);
}
