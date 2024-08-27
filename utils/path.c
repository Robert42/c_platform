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
    p.cstr[p.len] = *(path++);
  }
  debug_assert_usize_lte(p.len, PATH_LEN_MAX);
  p.cstr[p.len] = 0;

  return p;
}

Path path_truncate(Path p, usize len)
{
  if(len < p.len)
  {
    p.len = len;
    p.cstr[len] = 0;
  }
  return p;
}

Path path_parent(Path p)
{
  if(p.len == 1 && p.cstr[0] == '/')
    return p;
  for(ssize i=p.len-2; i>=0; --i)
  {
    if(p.cstr[i]=='/')
    {
      p.cstr[i] = 0;
      p.len = i;
      return p;
    }
  }

  return path_from_cstr(".");
}

// TODO: helper that appends a string to a path (modifying the filepath, not adding a slash)

Path path_concat(Path a, Path b)
{
  if(a.len == 0)
    return b;
  if(b.len == 0)
    return a;

  debug_assert_usize_lte(a.len + b.len, PATH_LEN_MAX);
  for(usize i=0; i<b.len; ++i)
    a.cstr[a.len++] = b.cstr[i];

  return a;
}

Path path_join(Path a, Path b)
{
  if(a.len == 0)
    return b;
  if(b.len == 0)
    return a;

  const bool need_slash = a.cstr[a.len-1] != '/';

  debug_assert_usize_lte(a.len+need_slash+b.len, PATH_LEN_MAX);
  if(need_slash)
    a.cstr[a.len++] = '/';

  return path_concat(a, b);
}

Path path_realpath(Path p)
{
  char* maybe_path = realpath(p.cstr, NULL);
  LINUX_ASSERT_NE(maybe_path, NULL);

  p = path_from_cstr(maybe_path);
  free(maybe_path);

  return p;
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
