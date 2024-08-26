// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "path.h"

void path_test()
{
  assert_bool_eq(path_is_c_file(""), false);
  assert_bool_eq(path_is_c_file("main.c"), true);
  assert_bool_eq(path_is_c_file("main.cpp"), false);
  assert_bool_eq(path_is_c_file("foo.h"), true);

  assert_bool_eq(path_is_c_file("bar.test.c"), true);
  assert_bool_eq(path_is_c_file(".c"), true);
  assert_bool_eq(path_is_c_file(".o"), false);
  assert_bool_eq(path_is_c_file("foo.c.tar.gz"), false);
  assert_bool_eq(path_is_c_file("c"), false);
}
