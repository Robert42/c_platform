// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "path.h"

Path path_from_cstr(const char* path)
{
  bool ok;
  Path p = _path_from_cstr(path, &ok);
  debug_assert_bool_eq(ok, true);
  return p;
}

Path _path_from_cstr(const char* path, bool* ok)
{
  *ok = true;

  Path p;
  for(p.len=0; *path!=0; ++p.len)
  {
    if(p.len == PATH_LEN_MAX)
    {
      *ok = false;
      break;
    }
    p.buffer[p.len] = *(path++);
  }
  debug_assert_usize_lte(p.len, PATH_LEN_MAX);
  p.buffer[p.len] = 0;

  return p;
}

Path path_truncate(Path p, usize len)
{
  if(len < p.len)
  {
    p.len = len;
    p.buffer[len] = 0;
  }
  return p;
}

Path path_parent(Path p)
{
  if(p.len == 1 && p.buffer[0] == '/')
    return p;
  for(ssize i=p.len-2; i>=0; --i)
  {
    if(p.buffer[i]=='/')
    {
      p.buffer[i] = 0;
      p.len = i;
      return p;
    }
  }

  return path_from_cstr(".");
}

bool path_is_c_file(const char* path)
{
  const usize len = strlen(path);
  if(len<2 || path[len-2] != '.')
    return false;
  switch(path[len-1])
  {
  case 'c':
  case 'h':
    return true;
  default:
    return false;
  }
}
