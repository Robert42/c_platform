// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

size_t __assert_capture__ = 0;
size_t __assert_caught__ = 0;

static void __assert_failed__()
{
  if(__assert_capture__)
  {
    __assert_caught__++;
    return;
  }

  printf("%s==== ASSERT ====%s\n", TERM_RED, TERM_NORMAL);
  abort();
}

#if ENV_DEBUG
#define DEBUG_VERSION_BIN(NAME, TY) void debug_assert_ ## NAME(TY x, TY y){assert_ ## NAME(x, y);}
#else
#define DEBUG_VERSION_BIN(NAME, TY) void debug_assert_ ## NAME(TY x, TY y){(void)x;(void)y;}
#endif
#define DEFINE_NUM(NAME, TY, OP) \
  void assert_ ## NAME(TY x, TY y){if(x OP y)return;else __assert_failed__(); } \
  DEBUG_VERSION_BIN(NAME, TY)
#define BIN_ASSERT_NUM_CMP(NAME, TY) \
  DEFINE_NUM(NAME ## _eq, TY, ==) \
  DEFINE_NUM(NAME ## _ne, TY, !=) \
  DEFINE_NUM(NAME ## _lt, TY, <) \
  DEFINE_NUM(NAME ## _lte, TY, <=) \
  DEFINE_NUM(NAME ## _gt, TY, >) \
  DEFINE_NUM(NAME ## _gte, TY, >=)

#include "assertions.h"
#undef BIN_ASSERT_NUM_CMP
#undef DEBUG_VERSION_BIN
#undef DEFINE_NUM

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
  if(__assert_capture__)
  {
    __assert_caught__++;
    return;
  }

  printf("%s==== ASSERT_LINUX ====%s\n", TERM_RED, TERM_RED_BOLD);
  perror(call);
  printf("%s%s:%d\n", TERM_NORMAL, __FILE__, __LINE__);
  abort();
}
#endif
