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
const char* TERM_MAGENTA = "";
const char* TERM_MAGENTA_BOLD = "";
const char* TERM_CYAN = "";
const char* TERM_CYAN_BOLD = "";

const char* TERM_NORMAL = "";
const char* TERM_CLEAR = "";
const char* TERM_CLEAR_LINE = "";

void term_init()
{
#ifdef __linux__
  bool is_terminal = isatty(STDOUT_FILENO) == 1;
#else
#error unimplemented
#endif
  
  if(is_terminal)
  {
#define ESCAPE "\x1B"

#define NORMAL "0"
#define BOLD "1"
#define RED_FG "31"
#define GREEN_FG "32"
#define YELLOW_FG "33"
#define BLUE_FG "34"
#define MAGENTA_FG "35"
#define CYAN_FG "36"
    TERM_RED = ESCAPE "[" NORMAL ";" RED_FG "m";
    TERM_RED_BOLD = ESCAPE "[" BOLD ";" RED_FG "m";
    TERM_GREEN = ESCAPE "[" NORMAL ";" GREEN_FG "m";
    TERM_GREEN_BOLD = ESCAPE "[" BOLD ";" GREEN_FG "m";
    TERM_YELLOW = ESCAPE "[" NORMAL ";" YELLOW_FG "m";
    TERM_YELLOW_BOLD = ESCAPE "[" BOLD ";" YELLOW_FG "m";
    TERM_BLUE = ESCAPE "[" NORMAL ";" BLUE_FG "m";
    TERM_BLUE_BOLD = ESCAPE "[" BOLD ";" BLUE_FG "m";
    TERM_MAGENTA = ESCAPE "[" NORMAL ";" MAGENTA_FG "m";
    TERM_MAGENTA_BOLD = ESCAPE "[" BOLD ";" MAGENTA_FG "m";
    TERM_CYAN = ESCAPE "[" NORMAL ";" CYAN_FG "m";
    TERM_CYAN_BOLD = ESCAPE "[" BOLD ";" CYAN_FG "m";
    TERM_NORMAL = ESCAPE "[" NORMAL "m";
    TERM_CLEAR = ESCAPE "[3J";
    TERM_CLEAR_LINE = ESCAPE "[0G" ESCAPE "[2K";
#undef ESCAPE
#undef BOLD
#undef NORMAL
#undef RED_FG
#undef GREEN_FG
#undef YELLOW_FG
#undef BLUE_FG
#undef MAGENTA_FG
#undef CYAN_FG
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
  printf("%s-- magenta normal --\n", TERM_MAGENTA);
  printf("%s-- magenta bold --\n", TERM_MAGENTA_BOLD);
  printf("%s-- cyan normal --\n", TERM_CYAN);
  printf("%s-- cyan bold --\n", TERM_CYAN_BOLD);
  printf("%s-- normal --\n", TERM_NORMAL);
}
