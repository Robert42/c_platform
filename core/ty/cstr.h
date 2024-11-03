// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#if ENV_COMPILER == COMPILER_TCC

#ifdef __linux__

int strcmp(const char* x, const char* y);
const char* strstr(const char* haystack, const char* needle);

#endif // __linux__

#else // ENV_COMPILER == COMPILER_TCC

#include <string.h>

#endif // ENV_COMPILER == COMPILER_TCC

bool char_is_ws(char x);

const char* cstr_trim_left(const char* x);
void cstr_trim_right(char* x);

char* cstr_to_lower(Mem_Region* region, const char* s);
void convert_cstr_to_lower(char* s);

char* cstr_to_upper(Mem_Region* region, const char* s);
void convert_cstr_to_upper(char* s);

char* cstr_copy(Mem_Region* region, const char* s);

usize cstr_to_usize(const char** s);

