// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "c_compiler.h"

enum C_Compiler C_COMPILER = CC_TCC;

void cc_compile_and_run(char* c_file, char* output_file)
{
  switch(C_COMPILER)
  {
  // If choosing libtcc, then simply fork and compile via the libtcc.
  case CC_TCC:
  {
    char* const args_compile[] = {"tcc", "-Wall", "-Werror", "-run", c_file, NULL};
    proc_exec_blocking(args_compile, (struct Proc_Exec_Blocking_Settings){});
    break;
  }
  case CC_GCC:
  {
    char* const args_compile[] = {"gcc", "-Wall", "-Werror", c_file, "-o", output_file, NULL};
    char* const args_test[] = {output_file, NULL};
    if(proc_exec_blocking(args_compile, (struct Proc_Exec_Blocking_Settings){}).exit_code == EXIT_SUCCESS)
      proc_exec_blocking(args_test, (struct Proc_Exec_Blocking_Settings){});
    break;
  }
  case CC_CLANG:
  {
    char* const args_compile[] = {"clang", "-Wall", "-Werror", c_file, "-o", output_file, NULL};
    char* const args_test[] = {output_file, NULL};
    if(proc_exec_blocking(args_compile, (struct Proc_Exec_Blocking_Settings){}).exit_code == EXIT_SUCCESS)
      proc_exec_blocking(args_test, (struct Proc_Exec_Blocking_Settings){});
    break;
  }
  }
}

enum C_Compiler cc_compiler_for_name(const char* name)
{
  if(strcmp(name, "tcc") == 0)
    return CC_TCC;
  else if(strcmp(name, "gcc") == 0)
    return CC_GCC;
  else if(strcmp(name, "clang") == 0)
    return CC_CLANG;
  else
    errx(EXIT_FAILURE, "Unknown compiler `%s`\n", name);
}
