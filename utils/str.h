// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

// TODO: tell the compilers & analyzers, that this is using printf formatting
char* cstr_fmt(Mem_Region* region, const char* fmt, ...);
char* str_fmt_va(Mem_Region* region, const char* fmt, va_list args);

