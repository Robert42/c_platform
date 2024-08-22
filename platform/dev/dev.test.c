// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "dev.h"

void dev_test()
{
  int xs[2];

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

  assert_ptr_eq(&xs[0], &xs[0]);
  EXPECT_ASSERT( assert_ptr_eq(&xs[0], &xs[1]); );
  EXPECT_ASSERT( assert_ptr_eq(&xs[1], &xs[0]); );

  debug_assert_usize_lt(0, 1);
  EXPECT_DEBUG_ASSERT( debug_assert_usize_lt(1, 1); );
  EXPECT_DEBUG_ASSERT( debug_assert_usize_lt(1, 0); );

  debug_assert_ptr_lte(&xs[0], &xs[1]);
  debug_assert_ptr_lte(&xs[0], &xs[0]);
  EXPECT_DEBUG_ASSERT( debug_assert_ptr_lte(&xs[1], &xs[0]); );

  EXPECT_DEBUG_ASSERT(
  EXPECT_DEBUG_ASSERT(
  );
  );
}
