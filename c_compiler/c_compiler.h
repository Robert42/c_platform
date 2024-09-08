// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

enum C_Compiler
{
  CC_TCC,
  CC_GCC,
  CC_CLANG,
};
#define CC_COUNT 3

void cc_compile_and_run(enum C_Compiler cc, Path c_file, Path output_file);
enum C_Compiler cc_compiler_for_name(const char* name); // will call errx, if the name is an unknown compiler
const char* cc_compiler_name(enum C_Compiler cc);

enum C_Compiler cc_fastest_available();
enum C_Compiler cc_best_optimizer_available();
bool cc_compiler_is_available(enum C_Compiler cc);

#define GCC_WARNING_OPTIONS \
  "-Wall", \
  "-Wextra", \
  "-Werror", \
  "-Wno-error=unused-parameter", \
  "-Wno-error=unused-variable", \
  "-Wno-error=sign-compare", \
  "-Werror=vla", \
  "-pedantic", \

#define GCC_SANITIZER_OPTIONS \
  "-fsanitize=address", \
  "-fsanitize=undefined", \

