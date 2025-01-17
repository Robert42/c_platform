// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "round.h"


bool is_power_of_two_or_zero_usize(usize x)
{
  return ((x-1) & x) == 0;
}

bool is_multiple_of_power_of_two_usize(usize x, usize y)
{
  debug_assert(is_power_of_two_or_zero_usize(y));
  debug_assert_usize_gt(y, 0);

  // y is a power of two and the compiler doesn't know it
  const usize result = (x & (y-1)) == 0;

  debug_assert_bool_eq(x % y == 0, result);

  return result;
}

usize ceil_multiple_of_usize(usize x, usize y)
{
  return y * ((x+y-1) / y);
}

usize ceil_multiple_of_power_of_two_usize(usize x, usize y)
{
  debug_assert(is_power_of_two_or_zero_usize(y));
  debug_assert_usize_gt(y, 0);

  const usize nonzero_bits = x & (y-1);
  const usize missing_to_next = 1 + (~nonzero_bits & (y-1));
  const usize result = nonzero_bits ? x + missing_to_next : x;
  debug_assert_bool_eq(ceil_multiple_of_usize(x, y), result);

  return result;
}

