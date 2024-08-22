// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

// ==== assertions ====

extern size_t __assert_capture__;
extern size_t __assert_caught__;

#define DECLARE_BIN(NAME, TY) \
  void assert_ ## NAME(TY x, TY y); \
  void debug_assert_ ## NAME(TY x, TY y);
#define BIN_ASSERT_NUM_CMP(NAME, TY) \
  DECLARE_BIN(NAME ## _eq, TY); \
  DECLARE_BIN(NAME ## _ne, TY); \
  DECLARE_BIN(NAME ## _lt, TY); \
  DECLARE_BIN(NAME ## _lte, TY); \
  DECLARE_BIN(NAME ## _gt, TY); \
  DECLARE_BIN(NAME ## _gte, TY);
#define BIN_ASSERT_CUSTOM(NAME, TY, CHECK) DECLARE_BIN(NAME, TY)
#include "assertions.h"
#undef BIN_ASSERT_NUM_CMP
#undef BIN_ASSERT_CUSTOM
#undef DECLARE_BIN

#define EXPECT_ASSERT(...) { \
  const size_t __prev__ = __assert_caught__; \
  __assert_capture__++; \
  {__VA_ARGS__} \
  __assert_capture__--; \
  assert_usize_lt(__prev__, __assert_caught__); \
}

#if ENV_DEBUG

#define EXPECT_DEBUG_ASSERT(...) EXPECT_ASSERT(__VA_ARGS__)
#define UNREACHABLE() abort()

#else // !ENV_DEBUG

#define EXPECT_DEBUG_ASSERT(...) {__VA_ARGS__}
#define UNREACHABLE() __builtin_unreachable()

#endif

#ifdef __linux__
void __linux_call_failed__(const char* call, const char* file, int line);
#define LINUX_ASSERT_EQ(CALL, SUCCESS) do{ if((CALL) != (SUCCESS)) {__linux_call_failed__(#CALL, __FILE__, __LINE__); } } while(0)
#define LINUX_ASSERT_NE(CALL, FAILURE) do{ if((CALL) == (FAILURE)) {__linux_call_failed__(#CALL, __FILE__, __LINE__); } } while(0)
#endif
