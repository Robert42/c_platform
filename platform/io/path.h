// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#define PATH_LEN_MAX 254 // 254 + nullterminator + len == 256

typedef struct
{
  char cstr[PATH_LEN_MAX+1];
  u8 len;
} Path;

Path path_from_cstr(const char* path);
Path _path_from_cstr(const char* path, bool* ok);

Path path_truncate(Path p, usize len);
Path path_parent(Path p);
Path path_append_char(Path a, char b);
Path path_append_cstr(Path a, const char* b);
Path path_concat(Path a, Path b);
Path path_join(Path a, Path b);
Path path_join_cstr_append_cstr(Path dir, const char* name_1, const char* name_2);
Path path_realpath(Path p);

bool path_is_c_file(const char* path);
bool path_has_suffix_one_of(const char* path, const char** suffix, usize suffix_count);

