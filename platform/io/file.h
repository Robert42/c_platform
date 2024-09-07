// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "path.h"

const char* file_text_read_to_cstr(Path p, Mem_Region* region);
void file_text_create_from_cstr(Path p, const char* str);
void file_text_create_from_cstr_if_different(Path p, const char* str);

// low level
void _create_file_from_bytes(const char* path, const void* bytes, usize num_bytes);
Bytes_Mut _read_all_file_bytes(const char* path, Mem_Region* region);
ssize _file_size(const char* path); // -1, if the file does not exist

