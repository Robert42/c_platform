// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

typedef struct _platform_io_Bytes
{
  u8* begin;
  u8* end;
} Bytes;

void _create_file_from_bytes(const char* path, const void* bytes, usize num_bytes);
Bytes _read_all_file_bytes(const char* path, Mem_Region* region);
ssize _file_size(const char* path); // -1, if the file does not exist


