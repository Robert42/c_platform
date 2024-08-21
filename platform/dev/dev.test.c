// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "dev.h"

void dev_test()
{
  EXPECT_ASSERT(
  EXPECT_ASSERT(
  );
  );

  assert_usize_eq(1, 1);
  EXPECT_ASSERT( assert_usize_eq(0, 1); );
  EXPECT_ASSERT( assert_usize_eq(1, 0); );

  assert_usize_lt(0, 1);
  EXPECT_ASSERT( assert_usize_lt(1, 1); );
  EXPECT_ASSERT( assert_usize_lt(1, 0); );

  assert_ptr_eq(1, 1);
  EXPECT_ASSERT( assert_ptr_eq(0, 1); );
  EXPECT_ASSERT( assert_ptr_eq(1, 0); );

  debug_assert_usize_lt(0, 1);
  EXPECT_DEBUG_ASSERT( debug_assert_usize_lt(1, 1); );
  EXPECT_DEBUG_ASSERT( debug_assert_usize_lt(1, 0); );

  debug_assert_ptr_lte(0, dev_test);
  debug_assert_ptr_lte(0, 0);
  EXPECT_DEBUG_ASSERT( debug_assert_ptr_lte(dev_test, 0); );

  EXPECT_DEBUG_ASSERT(
  EXPECT_DEBUG_ASSERT(
  );
  );
}
