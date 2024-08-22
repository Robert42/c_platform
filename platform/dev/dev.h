// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

// ==== assertions ====

extern size_t _assert_capture;
extern size_t _assert_captured;

#define DEFINE_BIN(NAME, TY) \
  void assert_ ## NAME(TY x, TY y); \
  void debug_assert_ ## NAME(TY x, TY y);
#define BIN_ASSERT_NUM_CMP(NAME, TY) \
  DEFINE_BIN(NAME ## _eq, TY); \
  DEFINE_BIN(NAME ## _ne, TY); \
  DEFINE_BIN(NAME ## _lt, TY); \
  DEFINE_BIN(NAME ## _lte, TY); \
  DEFINE_BIN(NAME ## _gt, TY); \
  DEFINE_BIN(NAME ## _gte, TY);
#include "assertions.h"
#undef BIN_ASSERT_NUM_CMP
#undef DEFINE_BIN

#define EXPECT_ASSERT(STMTS) { \
  const size_t __prev__ = _assert_captured; \
  _assert_capture++; \
  {STMTS} \
  _assert_capture--; \
  assert_usize_lt(__prev__, _assert_captured); \
}

#if ENV_DEBUG

#define EXPECT_DEBUG_ASSERT(STMTS) EXPECT_ASSERT(STMTS)
#define UNREACHABLE() abort()

#else // !ENV_DEBUG

#define EXPECT_DEBUG_ASSERT(STMTS) {STMTS}
#define UNREACHABLE() __builtin_unreachable()

#endif

#ifdef __linux__
void __linux_call_failed__(const char* call, const char* file, int line);
#define LINUX_ASSERT_EQ(CALL, SUCCESS) do{ if((CALL) != (SUCCESS)) {__linux_call_failed__(#CALL, __FILE__, __LINE__); } } while(0)
#define LINUX_ASSERT_NE(CALL, FAILURE) do{ if((CALL) == (FAILURE)) {__linux_call_failed__(#CALL, __FILE__, __LINE__); } } while(0)
#endif
