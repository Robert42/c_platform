// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

enum C_Compiler
{
  CC_TCC,
  CC_GCC,
  CC_CLANG,
};
void cc_compile_and_run(enum C_Compiler cc, char* c_file, char* output_file);
enum C_Compiler cc_compiler_for_name(const char* name); // will call errx, if the name is an unknown compiler

enum C_Compiler cc_fastest_available();
enum C_Compiler cc_best_optimizer_available();
bool cc_compiler_is_available(enum C_Compiler cc);

