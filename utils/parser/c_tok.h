// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

char* c_tok_parse_str_lit(Mem_Region* region, const char** code);
void c_tok_fmt_str_lit(Fmt* f, const char* content);

str tok_skip_ident(const char** code);

