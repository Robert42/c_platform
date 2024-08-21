// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

// ==== assertions ====

extern size_t _assert_capture;
extern size_t _assert_captured;

void assert_usize_eq(size_t x, size_t y);
void assert_ptr_eq(const void* x, const void* y);

void assert_usize_lt(size_t x, size_t y);

#define EXPECT_DEBUG_ASSERT(STMTS) { \
  const size_t __prev__ = _assert_captured; \
  _assert_capture++; \
  {STMTS} \
  _assert_capture--; \
  debug_assert_usize_lt(__prev__, _assert_captured); \
}
