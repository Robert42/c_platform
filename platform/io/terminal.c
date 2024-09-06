// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "terminal.h"

extern const char* TERM_STYLE_RED;
extern const char* TERM_STYLE_RED_BOLD;
extern const char* TERM_STYLE_RESET;

static const struct Term_Escape_Codes TERM_NONE = {
  .red = "",
  .red_bold = "",
  .green = "",
  .green_bold = "",
  .yellow = "",
  .yellow_bold = "",
  .blue = "",
  .blue_bold = "",
  .magenta = "",
  .magenta_bold = "",
  .cyan = "",
  .cyan_bold = "",

  .normal = "",
  .clear = "",
  .clear_line = "",
};

static const struct Term_Escape_Codes TERM_CONTROL_CODES = {
#define ESCAPE "\x1B"

#define NORMAL "0"
#define BOLD "1"
#define RED_FG "31"
#define GREEN_FG "32"
#define YELLOW_FG "33"
#define BLUE_FG "34"
#define MAGENTA_FG "35"
#define CYAN_FG "36"
    .red = ESCAPE "[" NORMAL ";" RED_FG "m",
    .red_bold = ESCAPE "[" BOLD ";" RED_FG "m",
    .green = ESCAPE "[" NORMAL ";" GREEN_FG "m",
    .green_bold = ESCAPE "[" BOLD ";" GREEN_FG "m",
    .yellow = ESCAPE "[" NORMAL ";" YELLOW_FG "m",
    .yellow_bold = ESCAPE "[" BOLD ";" YELLOW_FG "m",
    .blue = ESCAPE "[" NORMAL ";" BLUE_FG "m",
    .blue_bold = ESCAPE "[" BOLD ";" BLUE_FG "m",
    .magenta = ESCAPE "[" NORMAL ";" MAGENTA_FG "m",
    .magenta_bold = ESCAPE "[" BOLD ";" MAGENTA_FG "m",
    .cyan = ESCAPE "[" NORMAL ";" CYAN_FG "m",
    .cyan_bold = ESCAPE "[" BOLD ";" CYAN_FG "m",
    .normal = ESCAPE "[" NORMAL "m",
    .clear = ESCAPE "[3J",
    .clear_line = ESCAPE "[0G" ESCAPE "[2K",
#undef ESCAPE
#undef BOLD
#undef NORMAL
#undef RED_FG
#undef GREEN_FG
#undef YELLOW_FG
#undef BLUE_FG
#undef MAGENTA_FG
#undef CYAN_FG
};

struct Term_Escape_Codes TERM = {0};

/*@
  assigns TERM \from TERM_NONE, TERM_CONTROL_CODES;
*/
void term_init()
{
#ifdef __linux__
  bool is_terminal = isatty(STDOUT_FILENO) == 1;
#else
#error unimplemented
#endif
  
  if(is_terminal)
    TERM = TERM_CONTROL_CODES;
  else
    TERM = TERM_NONE;

  TERM_STYLE_RED = TERM.red;
  TERM_STYLE_RED_BOLD = TERM.red_bold;
  TERM_STYLE_RESET = TERM.normal;
}

void term_demo()
{
  printf("%s-- red normal --\n", TERM.red);
  printf("%s-- red bold --\n", TERM.red_bold);
  printf("%s-- green normal --\n", TERM.green);
  printf("%s-- green bold --\n", TERM.green_bold);
  printf("%s-- yellow normal --\n", TERM.yellow);
  printf("%s-- yellow bold --\n", TERM.yellow_bold);
  printf("%s-- blue normal --\n", TERM.blue);
  printf("%s-- blue bold --\n", TERM.blue_bold);
  printf("%s-- magenta normal --\n", TERM.magenta);
  printf("%s-- magenta bold --\n", TERM.magenta_bold);
  printf("%s-- cyan normal --\n", TERM.cyan);
  printf("%s-- cyan bold --\n", TERM.cyan_bold);
  printf("%s-- normal --\n", TERM.normal);
}
