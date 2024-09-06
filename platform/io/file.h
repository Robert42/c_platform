// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

void _create_file_from_bytes(const char* path, const void* bytes, usize num_bytes);
Bytes_Mut _read_all_file_bytes(const char* path, Mem_Region* region);
ssize _file_size(const char* path); // -1, if the file does not exist


