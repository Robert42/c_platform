// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

// ==== assertions ====

#if !ENV_STATIC_ANALYSIS
extern usize __assert_capture__;
extern usize __assert_caught__;
#endif

#include "assert.generated.h"

#define EXPECT_ASSERT(...) { \
  const usize __prev__ = __assert_caught__; \
  __assert_capture__++; \
  {__VA_ARGS__} \
  __assert_capture__--; \
  assert_usize_lt(__prev__, __assert_caught__); \
}

NORETURN
void __panic__(const char* title, const char* file, int line);

#define UNIMPLEMENTED() __panic__("UNIMPLEMENTED", __FILE__, __LINE__)
#define TODO() __panic__("TODO", __FILE__, __LINE__)

#if ENV_STATIC_ANALYSIS

#undef EXPECT_ASSERT
#define EXPECT_ASSERT(...) {}
#define EXPECT_DEBUG_ASSERT(...) {}
#define UNREACHABLE() abort()

#elif ENV_DEBUG

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

// ISSUE_FRAMA_C think about which assertions to keep, now that I am using frama_c
// - pro:
//   - frama_c is a analysis of all possible states
//   - less code to compile
//   - less assertions to wite
//   - there are plugins adding runtime verification if they were needed

