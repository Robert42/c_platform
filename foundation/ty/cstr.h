// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#if ENV_COMPILER == COMPILER_TCC

#ifdef __linux__

int strcmp(const char* x, const char* y);
const char* strstr(const char* haystack, const char* needle);
char* strtok(char* restrict str, const char* restrict delim);

#endif // __linux__

#else // ENV_COMPILER == COMPILER_TCC

#include <string.h>

#endif // ENV_COMPILER == COMPILER_TCC

