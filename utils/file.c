// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "file.h"

void create_text_file_cstr(Path p, const char* str)
{
  _create_file_from_bytes(p.cstr, str, strlen(str));
}

