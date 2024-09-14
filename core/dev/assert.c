// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#ifdef __linux__
#include <errno.h>
#endif
#if ENV_COMPILER != COMPILER_TCC
#include <stdio.h>
#endif

#if !ENV_STATIC_ANALYSIS
usize __assert_capture__ = 0;
usize __assert_caught__ = 0;
#endif

const char* TERM_STYLE_RED = "";
const char* TERM_STYLE_RED_BOLD = "";
const char* TERM_STYLE_RESET = "";

static void __bool_assert__(bool condition, const char* condition_code, const char* file, int line)
{
  if(LIKELY(condition))
    return;

#if !ENV_STATIC_ANALYSIS
  if(__assert_capture__)
  {
    __assert_caught__++;
    return;
  }
#endif

  printf("%s==== ASSERT ====%s\n", TERM_STYLE_RED, TERM_STYLE_RESET);
  printf("%s\n", condition_code);
  printf("\n");
  printf("%s:%i\n", file, line);
  printf("%s====%s\n", TERM_STYLE_RED, TERM_STYLE_RESET);
  abort();
}

static void __bin_assert_failed__(const char* condition, const char* lhs, const char* rhs, const char* file, int line)
{
#if !ENV_STATIC_ANALYSIS
  if(__assert_capture__)
  {
    __assert_caught__++;
    return;
  }
#endif

  printf("%s==== ASSERT ====%s\n", TERM_STYLE_RED, TERM_STYLE_RESET);
  printf("%s\n", condition);
  printf("\n");
  printf("lhs: %s\n", lhs);
  printf("rhs: %s\n", rhs);
  printf("\n");
  printf("%s:%i\n", file, line);
  printf("%s====%s\n", TERM_STYLE_RED, TERM_STYLE_RESET);
  abort();
}

static void __ter_assert_failed__(const char* condition, const char* lhs, const char* mid, const char* rhs, const char* file, int line)
{
#if !ENV_STATIC_ANALYSIS
  if(__assert_capture__)
  {
    __assert_caught__++;
    return;
  }
#endif

  printf("%s==== ASSERT ====%s\n", TERM_STYLE_RED, TERM_STYLE_RESET);
  printf("%s\n", condition);
  printf("\n");
  printf("lhs: %s\n", lhs);
  printf("mid: %s\n", mid);
  printf("rhs: %s\n", rhs);
  printf("\n");
  printf("%s:%i\n", file, line);
  printf("%s====%s\n", TERM_STYLE_RED, TERM_STYLE_RESET);
  abort();
}

void __panic__(const char* title, const char* file, int line, const char* msg, ...)
{
  printf("%s==== %s ====%s\n", TERM_STYLE_RED, title, TERM_STYLE_RESET);
  if(msg != NULL && msg[0]!=0)
  {
    va_list args;
    va_start(args, msg);
    vprintf(msg, args);
    va_end(args);
    printf("\n");
  }
  printf("%s:%i\n", file, line);
  printf("%s====%s\n", TERM_STYLE_RED, TERM_STYLE_RESET);
  abort();
}

static const char* fmt_bool(bool x)
{
  return x ? "true" : "false";
}

#include "assert.generated.c"

// ==== env ====

static inline const char* dev_env_compiler_name(int compiler_id)
{
#define CASE(X) case X: return #X;
  switch(compiler_id)
  {
  CASE(COMPILER_TCC)
  CASE(COMPILER_GCC)
  }
  abort();
#undef CASE
}

#ifdef __linux__
void __linux_call_failed__(const char* call, const char* file, int line)
{
#if !ENV_STATIC_ANALYSIS
  if(__assert_capture__)
  {
    __assert_caught__++;
    return;
  }
#endif

  printf("%s==== ASSERT_LINUX ====%s\n", TERM_STYLE_RED, TERM_STYLE_RED_BOLD);
  perror(call);
  printf("%s%s:%d\n", TERM_STYLE_RESET, file, line);
  abort();
}
#endif
