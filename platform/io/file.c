// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "file.h"

void file_text_create_from_cstr(Path p, const char* str)
{
  _create_file_from_bytes(p.cstr, str, strlen(str));
}

void file_text_create_from_cstr_if_different(const Path p, const char* str)
{
  bool already_exists_with_same_content = false;
  const usize len = strlen(str);

  const ssize file_size = _file_size(p.cstr);
  if(file_size>=0 && (usize)file_size == len)
  {
    const Mem_Region prev_stack = STACK;
    Bytes_Mut bytes = _read_all_file_bytes(p.cstr, &STACK);

    if(bytes_mut_len(bytes) == len && memcmp(bytes.begin, str, len)==0)
      already_exists_with_same_content = true;

    STACK = prev_stack;
  }

  if(!already_exists_with_same_content)
    _create_file_from_bytes(p.cstr, str, len);
}

