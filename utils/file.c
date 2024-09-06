// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "file.h"

void file_text_create_from_cstr(Path p, const char* str)
{
  _create_file_from_bytes(p.cstr, str, strlen(str));
}

void file_text_create_from_cstr_if_different(const Path p, const char* str)
{
  const usize len = strlen(str);

  const ssize file_size = _file_size(p.cstr);
  if(file_size>=0 && file_size == len)
  {
    // TODO: introduce STACK region
    Bytes_Mut bytes = _read_all_file_bytes(p.cstr, &SCRATCH);

    if(bytes.end - bytes.begin == len && memcmp(bytes.begin, str, len)==0)
      return;
  }

  _create_file_from_bytes(p.cstr, str, len);
}

