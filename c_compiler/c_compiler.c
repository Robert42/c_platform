// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "c_compiler.h"

void cc_compile_and_run(enum C_Compiler cc, Path c_file, Path output_file)
{
  switch(cc)
  {
  // If choosing libtcc, then simply fork and compile via the libtcc.
  case CC_TCC:
  {
    char* const args_compile[] = {"tcc", "-Wall", "-Werror", "-run", c_file.cstr, NULL};
    proc_exec_blocking(args_compile, (struct Proc_Exec_Blocking_Settings){0});
    break;
  }
  case CC_GCC:
  {
    char* const args_compile[] = {"gcc",
      "-std=c99",
      GCC_WARNING_OPTIONS
      "-g", GCC_SANITIZER_OPTIONS
      c_file.cstr,
      "-o", output_file.cstr,
      NULL};
    char* const args_test[] = {output_file.cstr, NULL};
    if(proc_exec_blocking(args_compile, (struct Proc_Exec_Blocking_Settings){0}).exit_code == EXIT_SUCCESS)
      proc_exec_blocking(args_test, (struct Proc_Exec_Blocking_Settings){0});
    break;
  }
  case CC_CLANG:
  {
    char* const args_compile[] = {"clang",
      "-std=c99",
      GCC_WARNING_OPTIONS
      "-g", GCC_SANITIZER_OPTIONS
      c_file.cstr,
      "-o", output_file.cstr,
      NULL};
    char* const args_test[] = {output_file.cstr, NULL};
    if(proc_exec_blocking(args_compile, (struct Proc_Exec_Blocking_Settings){0}).exit_code == EXIT_SUCCESS)
      proc_exec_blocking(args_test, (struct Proc_Exec_Blocking_Settings){0});
    break;
  }
  }
}

static const char* _CC_NAMES[CC_COUNT] = {
  [CC_TCC] = "tcc",
  [CC_GCC] = "gcc",
  [CC_CLANG] = "clang",
};
enum C_Compiler cc_compiler_for_name(const char* name)
{
  for(int i=0; i<CC_COUNT; ++i)
    if(strcmp(name, _CC_NAMES[i]) == 0)
      return (enum C_Compiler)i;
  errx(EXIT_FAILURE, "Unknown compiler `%s`\n", name);
}

const char* cc_compiler_name(enum C_Compiler cc)
{
  return _CC_NAMES[cc];
}

static enum C_Compiler _cc_find_available(const enum C_Compiler* compilers, int len)
{
  for(int i=0; i<len; ++i)
  {
    const enum C_Compiler cc = compilers[i];
    if(cc_compiler_is_available(cc))
      return cc;
  }
  errx(EXIT_FAILURE, "Could not find a c compiler");
}

enum C_Compiler cc_fastest_available()
{
  const enum C_Compiler FASTEST_FIRST[CC_COUNT] = {
    CC_TCC,
    CC_GCC,
    CC_CLANG,
  };

  return _cc_find_available(FASTEST_FIRST, ARRAY_LEN(FASTEST_FIRST));
}

enum C_Compiler cc_best_optimizer_available()
{
  const enum C_Compiler BEST_OPTIMIZER_FIRST[CC_COUNT] = {
    CC_CLANG,
    CC_GCC,
    CC_TCC,
  };

  return _cc_find_available(BEST_OPTIMIZER_FIRST, ARRAY_LEN(BEST_OPTIMIZER_FIRST));
}

bool cc_compiler_is_available(enum C_Compiler cc)
{
  char* const args_tcc[] = {"tcc", "-v", NULL};
  char* const args_gcc[] = {"gcc", "--version", NULL};
  char* const args_clang[] = {"clang", "--version", NULL};

  struct Proc_Exec_Blocking_Settings suppress_output = {
    .capture_stdout = true,
    .capture_stderr = true,
  };

  char* const * args = args_tcc;

  switch(cc)
  {
  case CC_TCC: args = args_tcc; break;
  case CC_GCC: args = args_gcc; break;
  case CC_CLANG: args = args_clang; break;
  }

  return proc_exec_blocking(args, suppress_output).exit_code == EXIT_SUCCESS;
}

