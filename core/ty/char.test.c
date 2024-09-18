// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

void char_test()
{
  assert_char_eq(ascii_to_lower('X'), 'x');
  assert_char_eq(ascii_to_lower('x'), 'x');
  assert_char_eq(ascii_to_lower('!'), '!');

  assert_char_eq(ascii_to_upper('x'), 'X');
  assert_char_eq(ascii_to_upper('X'), 'X');
  assert_char_eq(ascii_to_upper('!'), '!');
}

