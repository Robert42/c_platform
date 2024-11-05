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

static void _ccc_fmt_push_arg(const str arg, void* user_data) {fmt_write((Fmt*)user_data, "`%s` ", str_fmt(arg));}
static bool _ccc_fmt_end_cmd(void* user_data) {Fmt* f = (Fmt*)user_data; if(f->begin < f->end && f->end[-1]==' ')f->end--; fmt_write(f, "\n"); return true;}

const char* const _C_VERSION_NAME_GCC[] = {
  [C_VERSION_1989] = "c89",
  [C_VERSION_1999] = "c99",
  [C_VERSION_2011] = "c11",
  [C_VERSION_GNU_1989] = "gnu89",
  [C_VERSION_GNU_1999] = "gnu99",
  [C_VERSION_GNU_2011] = "gnu11",
};
const u32 _C_VERSION_WITH_EXTENSIONS = 0
  | (1 << C_VERSION_GNU_1989)
  | (1 << C_VERSION_GNU_1999)
  | (1 << C_VERSION_GNU_2011)
;

const char* const _C_COMPILER_CMD[] = {
  [CC_TCC] = "tcc",
  [CC_GCC] = "gcc",
  [CC_CLANG] = "clang",
};

const char* const _C_GCC_WARNING_OPTIONS[] = {
  "-Wall",
  "-Wextra",
  "-Werror",

  // warnings, but not errors
  "-Wno-error=unused-parameter",
  "-Wno-error=unused-variable",
  "-Wno-error=unused-function",
  "-Wno-error=unused-but-set-variable",
  "-Wno-error=sign-compare",
  "-Wno-error=uninitialized",
  "-Wno-error=pedantic",
};

const char* const _C_GCC_SANITIZER[] = {
  "-fsanitize=address",
  "-fsanitize=pointer-compare",
  "-fsanitize=pointer-subtract",
  "-fsanitize=undefined",
  "-fsanitize-address-use-after-scope",
  "-fstack-protector-all",
};

const char* const _C_TCC_WARNING_OPTIONS[] = {
  "-Wall",
  // "-Wunsupported",
  /*TODO: decide
  "-Wwrite-strings",
  */
  "-Werror",
};

static bool _ccc(struct C_Compiler_Config cfg, void* user_data, void (*push_arg)(const str arg, void* user_data), bool (*end_cmd)(void* user_data))
{
  const bool has_extensions = (1 << cfg.c_version) & _C_VERSION_WITH_EXTENSIONS;
  const bool run = cfg.run_args != NULL;

  push_arg(str_from_cstr(_C_COMPILER_CMD[cfg.cc]), user_data);

  if(cfg.debug)
  {
    switch(cfg.cc)
    {
    case CC_TCC:
    case CC_GCC:
    case CC_CLANG:
      push_arg(str_from_cstr("-g"), user_data);
      break;
    }
  }

  if(cfg.sanitize_memory)
  {
    switch(cfg.cc)
    {
    case CC_TCC:
      break;
    case CC_GCC:
    case CC_CLANG:
      for(usize i=0; i<ARRAY_LEN(_C_GCC_SANITIZER); ++i)
        push_arg(str_from_cstr(_C_GCC_SANITIZER[i]), user_data);
      break;
    }
  }

  switch(cfg.cc)
  {
  case CC_TCC:
    if(!cfg.skip_warning_flags)
      for(usize i=0; i<ARRAY_LEN(_C_TCC_WARNING_OPTIONS); ++i)
        push_arg(str_from_cstr(_C_TCC_WARNING_OPTIONS[i]), user_data);
    break;
  case CC_GCC:
  case CC_CLANG:
    {
      char _buf_std[16];
      Fmt f = fmt_new(_buf_std, sizeof(_buf_std));
      fmt_write(&f, "-std=%s", _C_VERSION_NAME_GCC[cfg.c_version]);
      push_arg((str){f.begin, f.end}, user_data);

      if(!has_extensions)
        push_arg(str_from_cstr("-pedantic"), user_data);

      if(!cfg.skip_warning_flags)
        for(usize i=0; i<ARRAY_LEN(_C_GCC_WARNING_OPTIONS); ++i)
          push_arg(str_from_cstr(_C_GCC_WARNING_OPTIONS[i]), user_data);

      if(cfg.disable_vla)
        push_arg(str_from_cstr("-Werror=vla"), user_data);
    }
    break;
  }

  if(cfg.cc==CC_TCC && run)
    push_arg(STR_LIT("-run"), user_data);
  else if(cfg.output_file.len > 0)
  {
    push_arg(str_from_cstr("-o"), user_data);
    push_arg(path_as_str(&cfg.output_file), user_data);
  }

  push_arg(path_as_str(&cfg.c_file), user_data);

  if(run)
  {
    switch(cfg.cc)
    {
    case CC_TCC:
      break;
    case CC_GCC:
    case CC_CLANG:
      if(!end_cmd(user_data))
        return user_data;
      push_arg(path_as_str(&cfg.output_file), user_data);
      break;
    }
    for(usize i=0; i<cfg.run_args_count; ++i)
      push_arg(str_from_cstr(cfg.run_args[i]), user_data);
  }

  return end_cmd(user_data);
}

struct _Runner
{
  Mem_Region* region;
  Mem_Region region_prev;
  char* args[128];
  usize arg_count;
};

static void _ccc_runner_push_arg(const str arg, struct _Runner* runner)
{
  assert_usize_lt(runner->arg_count, sizeof(runner->args));
  runner->args[runner->arg_count++] = str_fmt_to_region(runner->region, arg);
}
static bool _ccc_runner_end_cmd(struct _Runner* runner)
{
  assert_usize_lt(runner->arg_count, sizeof(runner->args));
  runner->args[runner->arg_count] = NULL;

  const struct Proc_Exec_Blocking_Result result = proc_exec_blocking(runner->args, (struct Proc_Exec_Blocking_Settings){
  });

  *runner->region = runner->region_prev;
  runner->arg_count = 0;

  return result.success;
}

static void _ccc_run_push_arg(const str arg, void* user_data) {_ccc_runner_push_arg(arg, (struct _Runner*)user_data);}
static bool _ccc_run_end_cmd(void* user_data) {return _ccc_runner_end_cmd((struct _Runner*)user_data);}

bool cc_run(struct C_Compiler_Config cfg)
{
  debug_assert_bool_eq(_CC_INIT_CALLED, true); // ensure cc_init was called

  struct _Runner runner = {
    .region = &STACK,
    .region_prev = STACK,
  };

  if(cfg.gen_parent_dir && cfg.output_file.len > 0)
    mkpath(path_parent(cfg.output_file));

  return _ccc(cfg, &runner, _ccc_run_push_arg, _ccc_run_end_cmd);
}

void cc_command_fmt(Fmt* f, struct C_Compiler_Config cfg)
{
  _ccc(cfg, f, _ccc_fmt_push_arg, _ccc_fmt_end_cmd);
}

bool cc_compile_and_run(enum C_Compiler cc, Path c_file, Path output_file)
{
  const char* no_args;
  struct C_Compiler_Config cfg = {
    .cc = cc,
    .c_version = C_VERSION_GNU_1999,
    .debug = true,
    .disable_vla = true,
    .skip_warning_flags = false,
    .sanitize_memory = !DISABLE_SANITIZER,
    .c_file = c_file,
    .output_file = output_file,
    .run_args = &no_args,
    .run_args_count = 0,
    .capture_run_output = false,
  };

#if 0
  {
    char buf[4096] = {};
    Fmt f = fmt_new(buf, sizeof(buf));
    cc_command_fmt(&f, cfg);
    printf("==== cc_compile_and_run ====\n%s\n====\n", f.begin);
  }
#endif

  return cc_run(cfg);
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

enum C_Version cc_version_for_name(const char* name)
{
  for(int i=0; i<CC_COUNT; ++i)
    if(cstr_eq(name, _C_VERSION_NAME_GCC[i]))
      return (enum C_Version)i;
  errx(EXIT_FAILURE, "Unknown version `%s`\n", name);
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

