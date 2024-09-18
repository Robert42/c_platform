// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#define CASE_OFFSET ('x'-'X')

char ascii_to_lower(char x)
{
  switch(x)
  {
  case 'A' ... 'Z':
    return x + CASE_OFFSET;
  default:
    return x;
  }
}

char ascii_to_upper(char x)
{
  switch(x)
  {
  case 'a' ... 'z':
    return x - CASE_OFFSET;
  default:
    return x;
  }
}

#undef CASE_OFFSET
