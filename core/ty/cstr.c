// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

bool char_is_ws(char x)
{
  switch(x)
  {
  case '\n':
    return true;
  default: return false;
  }
}

void cstr_trim_right(char* xs)
{
  usize i = strlen(xs);
  if(char_is_ws(xs[i-1]))
     xs[i-1] = 0;
}
