// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

enum C_Compiler
{
  CC_TCC,
  CC_GCC,
  CC_CLANG,
};
#define CC_COUNT 3

bool cc_compile_and_run(enum C_Compiler cc, Path c_file, Path output_file);
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
  "-Wno-error=unused-function", \
  "-Wno-error=unused-but-set-variable", \
  "-Wno-error=sign-compare", \
  "-Wno-error=uninitialized", \
  "-Wno-error=pedantic", \
  "-Werror=vla", \

#define GCC_SANITIZER_OPTIONS \
  "-fsanitize=address", \
  "-fsanitize=pointer-compare", \
  "-fsanitize=pointer-subtract", \
  "-fsanitize=undefined", \
  "-fsanitize-address-use-after-scope", \
  "-fstack-protector-all", \

#if 1
// gcc extensions I like
// - case ranges (`case 'a' ... 'z':`)
// - binary integer literals (`0b000:`)
// - binary integer literal separators (`0b1000'0000:`)
#define C_STANDARD "-std=gnu99"
#else
#define C_STANDARD "-std=c99", "-pedantic"
#endif

void cc_init();

