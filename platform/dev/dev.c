// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#if !ENV_STATIC_ANALYSIS
usize __assert_capture__ = 0;
usize __assert_caught__ = 0;
#endif

// TODO: move to a header
char* cstr_fmt(Mem_Region* region, const char* fmt, ...);

static void __assert_failed__()
{
#if !ENV_STATIC_ANALYSIS
  if(__assert_capture__)
  {
    __assert_caught__++;
    return;
  }
#endif

  printf("%s==== ASSERT ====%s\n", TERM.red, TERM.normal);
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

  printf("%s==== ASSERT ====%s\n", TERM.red, TERM.normal);
  printf("%s\n", condition);
  printf("\n");
  printf("lhs: %s\n", lhs);
  printf("rhs: %s\n", rhs);
  printf("\n");
  printf("%s:%i", file, line);
  printf("%s====%s\n", TERM.red, TERM.normal);
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

  printf("%s==== ASSERT ====%s\n", TERM.red, TERM.normal);
  printf("%s\n", condition);
  printf("\n");
  printf("lhs: %s\n", lhs);
  printf("mid: %s\n", mid);
  printf("rhs: %s\n", rhs);
  printf("\n");
  printf("%s:%i", file, line);
  printf("%s====%s\n", TERM.red, TERM.normal);
  abort();
}

static const char* fmt_bool(bool x)
{
  return x ? "true" : "false";
}

#include "assert.c"

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

void dev_env_demo()
{
  printf("ENV_DEBUG: %i\n", ENV_DEBUG);
  printf("ENV_COMPILER: %s\n", dev_env_compiler_name(ENV_COMPILER));
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

  printf("%s==== ASSERT_LINUX ====%s\n", TERM.red, TERM.red_bold);
  perror(call);
  printf("%s%s:%d\n", TERM.normal, __FILE__, __LINE__);
  abort();
}
#endif
