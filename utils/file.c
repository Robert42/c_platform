// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "file.h"

void file_text_create_from_cstr(Path p, const char* str)
{
  _create_file_from_bytes(p.cstr, str, strlen(str));
}

