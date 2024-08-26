// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

enum C_Compiler
{
  CC_TCC,
  CC_GCC,
  CC_CLANG,
};
extern enum C_Compiler C_COMPILER;

void cc_compile_and_run(char* c_file, char* output_file);
enum C_Compiler cc_compiler_for_name(const char* name); // will call errx, if the name is an unknown compiler

