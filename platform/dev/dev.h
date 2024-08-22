// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

// ==== assertions ====

extern size_t _assert_capture;
extern size_t _assert_captured;

void assert_usize_eq(size_t x, size_t y);
void assert_usize_lt(size_t x, size_t y);
void assert_ptr_eq(const void* x, const void* y);

void debug_assert_usize_lt(size_t x, size_t y);
void debug_assert_ptr_lte(const void* x, const void* y);

#define EXPECT_ASSERT(STMTS) { \
  const size_t __prev__ = _assert_captured; \
  _assert_capture++; \
  {STMTS} \
  _assert_capture--; \
  assert_usize_lt(__prev__, _assert_captured); \
}

#if ENV_DEBUG
#define EXPECT_DEBUG_ASSERT(STMTS) EXPECT_ASSERT(STMTS)
#else
#define EXPECT_DEBUG_ASSERT(STMTS) {STMTS}
#endif

#ifdef __linux__
void __linux_call_failed__(const char* call, const char* file, int line);
#define LINUX_ASSERT_EQ(CALL, SUCCESS) do{ if((CALL) != (SUCCESS)) {__linux_call_failed__(#CALL, __FILE__, __LINE__); } } while(0)
#endif
