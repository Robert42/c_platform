// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

void math_round_test()
{
  assert_bool_eq(is_power_of_two_or_zero_usize(0), true);
  assert_bool_eq(is_power_of_two_or_zero_usize(1), true);
  assert_bool_eq(is_power_of_two_or_zero_usize(2), true);
  assert_bool_eq(is_power_of_two_or_zero_usize(3), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(4), true);
  assert_bool_eq(is_power_of_two_or_zero_usize(5), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(6), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(7), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(8), true);
  assert_bool_eq(is_power_of_two_or_zero_usize(9), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(10), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(11), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(12), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(13), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(14), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(15), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(16), true);
  assert_bool_eq(is_power_of_two_or_zero_usize(17), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(18), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(19), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(20), false);
  assert_bool_eq(is_power_of_two_or_zero_usize(26), false);
}

