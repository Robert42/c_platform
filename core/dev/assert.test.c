// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "assert.h"

void assert_test()
{
  int xs[2];

  EXPECT_ASSERT(
  EXPECT_ASSERT(
  );
  );

  assert_usize_eq(1, 1);
  assert_usize_eq(0, 0);
  EXPECT_ASSERT( assert_usize_eq(0, 1); );
  EXPECT_ASSERT( assert_usize_eq(1, 0); );

  assert_usize_ne(42, 37);
  assert_usize_ne(37, 42);
  EXPECT_ASSERT( assert_usize_ne(37, 37); );
  EXPECT_ASSERT( assert_usize_ne(42, 42); );

  assert_usize_lt(0, 1);
  EXPECT_ASSERT( assert_usize_lt(0, 0); );
  EXPECT_ASSERT( assert_usize_lt(1, 1); );
  EXPECT_ASSERT( assert_usize_lt(1, 0); );

  assert_usize_lte(42, 42);
  assert_usize_lte(37, 37);
  assert_usize_lte(37, 42);
  EXPECT_ASSERT( assert_usize_lte(42, 37); );

  assert_usize_gt(42, 37);
  EXPECT_ASSERT( assert_usize_gt(42, 42); );
  EXPECT_ASSERT( assert_usize_gt(37, 37); );
  EXPECT_ASSERT( assert_usize_gt(37, 42); );

  assert_usize_gte(42, 42);
  assert_usize_gte(37, 37);
  assert_usize_gte(42, 37);
  EXPECT_ASSERT( assert_usize_gte(37, 42); );

  EXPECT_ASSERT( assert_usize_lte_lt(42, 37, 137); );
  assert_usize_lte_lt(37, 42, 137);
  assert_usize_lte_lt(42, 42, 137);
  EXPECT_ASSERT( assert_usize_lte_lt(43, 42, 137); );
  EXPECT_ASSERT( assert_usize_lte_lt(37, 42, 42); );
  assert_usize_lte_lt(37, 42, 43);
  EXPECT_ASSERT( assert_usize_lte_lt(37, 42, 41); );

  EXPECT_ASSERT( assert_usize_lte_lte(42, 37, 137); );
  assert_usize_lte_lte(37, 42, 137);
  assert_usize_lte_lte(42, 42, 137);
  EXPECT_ASSERT( assert_usize_lte_lte(43, 42, 137); );
  assert_usize_lte_lte(37, 42, 42);
  assert_usize_lte_lte(37, 42, 43);
  EXPECT_ASSERT( assert_usize_lte_lte(37, 42, 41); );

  assert_ptr_eq(&xs[0], &xs[0]);
  EXPECT_ASSERT( assert_ptr_eq(&xs[0], &xs[1]); );
  EXPECT_ASSERT( assert_ptr_eq(&xs[1], &xs[0]); );

  assert_cstr_eq("", "");
  assert_cstr_eq("xyz", "xyz");
  EXPECT_ASSERT( assert_cstr_eq("", "xyz"); );
  EXPECT_ASSERT( assert_cstr_eq("xyz", "x"); );
  EXPECT_ASSERT( assert_cstr_eq("xyz", "xyw"); );

  debug_assert_usize_lt(0, 1);
  EXPECT_DEBUG_ASSERT( debug_assert_usize_lt(1, 1); );
  EXPECT_DEBUG_ASSERT( debug_assert_usize_lt(1, 0); );

  debug_assert_ptr_lte(&xs[0], &xs[1]);
  debug_assert_ptr_lte(&xs[0], &xs[0]);
  EXPECT_DEBUG_ASSERT( debug_assert_ptr_lte(&xs[1], &xs[0]); );

  debug_assert_bool_eq(true, true);
  debug_assert_bool_eq(false, false);
  EXPECT_DEBUG_ASSERT( debug_assert_bool_eq(true, false); );

  EXPECT_DEBUG_ASSERT(
  EXPECT_DEBUG_ASSERT(
  );
  );

  EXPECT_DEBUG_ASSERT(
  debug_assert(false);
  );
  EXPECT_ASSERT(
  assert(false);
  );
  debug_assert(true);
  assert(true);
  
  // assert(false); // prints `false` instead of `((_Bool)0)`
}
