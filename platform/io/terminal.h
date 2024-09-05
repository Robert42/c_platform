// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct Term_Escape_Codes
{
  // ==== style ====
  const char* red;
  const char* red_bold;
  const char* green;
  const char* green_bold;
  const char* yellow;
  const char* yellow_bold;
  const char* blue;
  const char* blue_bold;
  const char* magenta;
  const char* magenta_bold;
  const char* cyan;
  const char* cyan_bold;

  const char* normal;

  // ==== clear ====
  const char* clear;
  const char* clear_line;
};

extern struct Term_Escape_Codes TERM;

void term_init();
void term_demo();
