// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

usize __assert_capture__ = 0;
usize __assert_caught__ = 0;

NORETURN
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

NORETURN
static void __bin_assert_failed__(const char* lhs, const char* rhs)
{
  if(__assert_capture__)
  {
    __assert_caught__++;
    return;
  }

  printf("%s==== ASSERT ====%s\n", TERM_RED, TERM_NORMAL);
  printf("lhs: %s\n", lhs);
  printf("rhs: %s\n", rhs);
  abort();
}

static const char* fmt_bool(bool x)
{
  return x ? "true" : "false";
}

#if ENV_DEBUG
#define DEBUG_VERSION_BIN(NAME, TY) void debug_assert_ ## NAME(TY x, TY y){assert_ ## NAME(x, y);}
#define DEBUG_VERSION_RNG(NAME, TY) void debug_assert_ ## NAME(TY x, TY y, TY z){assert_ ## NAME(x, y, z);}
#else
#define DEBUG_VERSION_BIN(NAME, TY) void debug_assert_ ## NAME(TY x, TY y){(void)x;(void)y;}
#define DEBUG_VERSION_RNG(NAME, TY) void debug_assert_ ## NAME(TY x, TY y, TY z){(void)x;(void)y;(void)z;}
#endif
#define DEFINE_NUM_BIN(NAME, TY, OP) \
  void assert_ ## NAME(TY x, TY y){if(x OP y)return;else __assert_failed__(); } \
  DEBUG_VERSION_BIN(NAME, TY)
#define DEFINE_NUM_RNG(NAME, TY, OP1, OP2) \
  void assert_ ## NAME(TY x, TY y, TY z){ if((x OP1 y) && (y OP2 z))return;else __assert_failed__(); } \
  DEBUG_VERSION_RNG(NAME, TY)
#define BIN_ASSERT_NUM_CMP(NAME, TY) \
  DEFINE_NUM_BIN(NAME ## _eq, TY, ==) \
  DEFINE_NUM_BIN(NAME ## _ne, TY, !=) \
  DEFINE_NUM_BIN(NAME ## _lt, TY, <) \
  DEFINE_NUM_BIN(NAME ## _lte, TY, <=) \
  DEFINE_NUM_BIN(NAME ## _gt, TY, >) \
  DEFINE_NUM_BIN(NAME ## _gte, TY, >=)
#define RNG_ASSERT_NUM_CMP(NAME, TY) \
  DEFINE_NUM_RNG(NAME ## _lte_lte, TY, <=, <=) \
  DEFINE_NUM_RNG(NAME ## _lte_lt, TY, <=, <)
#define BIN_ASSERT_CUSTOM(NAME, TY, CHECK, FMT) void assert_ ## NAME(TY x, TY y){if(CHECK)return;else __bin_assert_failed__(FMT(x), FMT(y)); } DEBUG_VERSION_BIN(NAME, TY)
#include "assertions.h"
#undef BIN_ASSERT_NUM_CMP
#undef RNG_ASSERT_NUM_CMP
#undef BIN_ASSERT_CUSTOM
#undef DEBUG_VERSION_BIN
#undef DEFINE_NUM_BIN
#undef DEFINE_NUM_RNG

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
NORETURN
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
