// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "c_compiler.h"

#ifndef DISABLE_SANITIZER
#define DISABLE_SANITIZER 0
#endif

#if ENV_DEBUG
bool _CC_INIT_CALLED = false;
#endif

void cc_init()
{
#if ENV_DEBUG
  debug_assert_bool_eq(_CC_INIT_CALLED, false); // ensure cc_init is called once
  _CC_INIT_CALLED = true;
#endif

  char ASAN_OPTIONS[] = "ASAN_OPTIONS=detect_stack_use_after_return=1,detect_invalid_pointer_pairs=2";

  const int putenv_result = putenv(ASAN_OPTIONS);
#ifdef __linux__
  LINUX_ASSERT_EQ(putenv_result, 0);
#else
  assert_int_eq(putenv_result, 0);
#endif
}

static void _ccc_count_incr_push_arg(const str arg, void* user_data) {(void)arg;*(usize*)user_data += 1;}
static void _ccc_count_incr_end_cmd(void* user_data) {*(usize*)user_data += 1;}
static void _ccc_fmt_push_arg(const str arg, void* user_data) {fmt_write((Fmt*)user_data, "`%s` ", str_fmt(arg));}
static void _ccc_fmt_end_cmd(void* user_data) {Fmt* f = (Fmt*)user_data; if(f->begin < f->end && f->end[-1]==' ')f->end--; fmt_write(f, "\n");}

static void _ccc(struct C_Compiler_Config cfg, void* user_data, void (*push_arg)(const str arg, void* user_data), void (*end_cmd)(void* user_data))
{
  debug_assert_bool_eq(_CC_INIT_CALLED, true); // ensure cc_init was called

  switch(cfg.cc)
  {
  case CC_TCC:
    TODO();
  case CC_GCC:
    push_arg(str_from_cstr("gcc"), user_data);
    break;
  case CC_CLANG:
    TODO();
  }

  switch(cfg.c_version)
  {
  case C_VERSION_1989:
    push_arg(str_from_cstr("-std=c89"), user_data);
    break;
  case C_VERSION_1999:
    push_arg(str_from_cstr("-std=c99"), user_data);
    break;
  case C_VERSION_2011:
    push_arg(str_from_cstr("-std=c11"), user_data);
    break;
  }

  push_arg(path_as_str(&cfg.c_file), user_data);

  push_arg(str_from_cstr("-o"), user_data);
  push_arg(path_as_str(&cfg.output_file), user_data);

  // TODO: cfg.run_args

  end_cmd(user_data);
}

void cc_command_fmt(Fmt* f, struct C_Compiler_Config cfg)
{
  _ccc(cfg, f, _ccc_fmt_push_arg, _ccc_fmt_end_cmd);
}

bool cc_compile_and_run(enum C_Compiler cc, Path c_file, Path output_file)
{
  debug_assert_bool_eq(_CC_INIT_CALLED, true); // ensure cc_init was called

  switch(cc)
  {
  // If choosing libtcc, then simply fork and compile via the libtcc.
  case CC_TCC:
  {
    char* const args_compile[] = {"tcc", "-Wall", "-Werror", "-run", c_file.cstr, NULL};
    return proc_exec_blocking(args_compile, (struct Proc_Exec_Blocking_Settings){0}).success;
  }
  case CC_GCC:
  {
    char* const args_compile[] = {"gcc",
      C_STANDARD,
      GCC_WARNING_OPTIONS
      "-g",
#if !DISABLE_SANITIZER
      GCC_SANITIZER_OPTIONS
#endif
      c_file.cstr,
      "-o", output_file.cstr,
      NULL};
    char* const args_test[] = {output_file.cstr, NULL};
    if(!proc_exec_blocking(args_compile, (struct Proc_Exec_Blocking_Settings){0}).success)
      return false;
    return proc_exec_blocking(args_test, (struct Proc_Exec_Blocking_Settings){0}).success;
  }
  case CC_CLANG:
  {
    char* const args_compile[] = {"clang",
      C_STANDARD,
      GCC_WARNING_OPTIONS
      "-g",
#if !DISABLE_SANITIZER
      GCC_SANITIZER_OPTIONS
#endif
      c_file.cstr,
      "-o", output_file.cstr,
      NULL};
    char* const args_test[] = {output_file.cstr, NULL};
    if(!proc_exec_blocking(args_compile, (struct Proc_Exec_Blocking_Settings){0}).success)
      return false;
    return proc_exec_blocking(args_test, (struct Proc_Exec_Blocking_Settings){0}).success;
  }
  }

  UNREACHABLE();
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

  return proc_exec_blocking(args, suppress_output).success;
}

