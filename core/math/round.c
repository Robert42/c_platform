// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "round.h"


bool is_power_of_two_or_zero_usize(usize x)
{
  return ((x-1) & x) == 0;
}

usize ceil_multiple_of(usize x, usize y)
{
  return y * ((x+y-1) / y);
}

usize ceil_multiple_of_power_of_two_usize(usize x, usize y)
{
  debug_assert(is_power_of_two_or_zero_usize(y));
  debug_assert_usize_gt(y, 0);
  const usize result = ceil_multiple_of(x, y);
  return result;
}

