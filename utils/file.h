// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

const char* file_text_read_to_cstr(Path p, Mem_Region* region);
void file_text_create_from_cstr(Path p, const char* str);
void file_text_create_from_cstr_if_different(Path p, const char* str);

