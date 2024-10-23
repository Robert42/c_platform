// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

bool char_is_ws(char x)
{
  switch(x)
  {
  case ' ':
  case '\t':
  case '\n':
    return true;
  default: return false;
  }
}

const char* cstr_trim_left(const char* x)
{
  while(char_is_ws(*x))
    ++x;
  return x;
}

void cstr_trim_right(char* xs)
{
  usize i = strlen(xs);
  while(i>0 && char_is_ws(xs[i-1]))
     xs[--i] = 0;
}

char* cstr_to_lower(Mem_Region* region, const char* s)
{
  char* xs = (char*)mem_region_alloc_bytes_unaligned(region, strlen(s)+1);
  for(char* x=xs; ; ++s, ++x)
  {
    *x = ascii_to_lower(*s);
    if(*s == 0)
      break;
  }
  return xs;
}

void convert_cstr_to_lower(char* s)
{
  for(; *s != 0; ++s)
  {
    *s = ascii_to_lower(*s);
  }
}

char* cstr_to_upper(Mem_Region* region, const char* s)
{
  char* xs = (char*)mem_region_alloc_bytes_unaligned(region, strlen(s)+1);
  for(char* x=xs; ; ++s, ++x)
  {
    *x = ascii_to_upper(*s);
    if(*s == 0)
      break;
  }
  return xs;
}

void convert_cstr_to_upper(char* s)
{
  for(; *s != 0; ++s)
    *s = ascii_to_upper(*s);
}

