// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#define PATH_LEN_MAX 254 // 254 + nullterminator + len == 256

typedef struct
{
  char buffer[PATH_LEN_MAX+1];
  u8 len;
} Path;

Path path_from_cstr(const char* path);
Path _path_from_cstr(const char* path, bool* ok);

bool path_is_c_file(const char* path);
