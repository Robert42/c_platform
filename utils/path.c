// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

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
