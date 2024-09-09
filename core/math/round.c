// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "round.h"


bool is_power_of_two_or_zero_usize(usize x)
{
  return ((x-1) & x) == 0;
}
