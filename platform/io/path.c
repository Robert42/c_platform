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

Path path_append_char(Path a, char c)
{
  debug_assert_usize_lt(a.len, PATH_LEN_MAX);
  a.cstr[a.len++] = c;
  a.cstr[a.len] = 0;

  return a;
}

Path path_append_cstr(Path a, const char* b)
{
  return path_concat(a, path_from_cstr(b));
}

Path path_concat(Path a, Path b)
{
  if(a.len == 0)
    return b;
  return path_concat_skipping(a, b, 0);
}

Path path_concat_skipping(Path a, Path b, usize skip)
{
  debug_assert_usize_lte(a.len + b.len, PATH_LEN_MAX);
  for(usize i=skip; i<b.len; ++i)
    a.cstr[a.len++] = b.cstr[i];
  a.cstr[a.len] = 0;

  return a;
}

Path path_join(Path a, Path b)
{
  if(a.len == 0)
    return b;
  if(b.len == 0)
    return a;

  if(a.cstr[a.len-1] != '/')
    a = path_append_char(a, '/');

  usize skip = 0;
  if(b.cstr[0] == '.' && b.cstr[1] == '/')
    skip += 2;

  return path_concat_skipping(a, b, skip);
}

Path path_join_cstr_append_cstr(Path dir, const char* name_1, const char* name_2)
{
  return path_join(dir, path_append_cstr(path_from_cstr(name_1), name_2));
}

#ifdef __linux__
Path path_realpath(Path p)
{
  const Mem_Region _stack_restore = STACK;
  char* buffer = (char*)mem_region_alloc_bytes_unaligned(&STACK, MAXPATHLEN);

  char* maybe_path = realpath(p.cstr, buffer);
  LINUX_ASSERT_NE(maybe_path, NULL);

  p = path_from_cstr(maybe_path);

  STACK = _stack_restore;

  return p;
}
#endif

str path_as_str(const Path* p)
{
  return (str){p->cstr, p->cstr + p->len};
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

bool path_has_suffix_one_of(const char* path, const char** suffix, usize suffix_count)
{
  const usize len = strlen(path);
  str path_str = {path, path+len};

  for(usize i=0; i<suffix_count; ++i)
  {
    const str suffix_str = str_from_cstr_len(suffix[i], strlen(suffix[i]));
    if(str_ends_with(path_str, suffix_str))
      return true;
  }

  return false;
}
