// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "path.h"

void path_test()
{
  assert_usize_eq(sizeof(Path), 256);

  // ==== path_from_cstr ====
  assert_cstr_eq(path_from_cstr("x").buffer, "x");
  {
    char too_long[PATH_LEN_MAX + 2] = {};
    for(usize i=0; i<PATH_LEN_MAX; ++i)
      too_long[i] = 'x';
    const Path p_max = path_from_cstr(too_long);
    assert_cstr_eq(p_max.buffer, too_long);
    assert_usize_eq(p_max.len, PATH_LEN_MAX);

    too_long[PATH_LEN_MAX] = 'x';
    bool ok;
    const Path p_too_small = _path_from_cstr(too_long, &ok);
    assert_bool_eq(ok, false);
    assert_usize_eq(p_too_small.len, PATH_LEN_MAX);
  }

  // ==== path_truncate ====
  assert_cstr_eq(path_truncate(path_from_cstr("/a/b/c"), 1024).buffer, "/a/b/c");
  assert_cstr_eq(path_truncate(path_from_cstr("/a/b/c"), 3).buffer, "/a/");
  assert_usize_eq(path_truncate(path_from_cstr("/a/b/c"), 3).len, 3);

  // ==== path_parent ====
  assert_cstr_eq(path_parent(path_from_cstr("/abc/uvw/xyz/")).buffer, "/abc/uvw");
  assert_cstr_eq(path_parent(path_from_cstr("/abc/uvw/xyz")).buffer, "/abc/uvw");
  assert_cstr_eq(path_parent(path_from_cstr("/abc/uvw/xy")).buffer, "/abc/uvw");
  assert_cstr_eq(path_parent(path_from_cstr("/abc/uvw/x")).buffer, "/abc/uvw");
  assert_cstr_eq(path_parent(path_from_cstr("abc")).buffer, ".");
  assert_cstr_eq(path_parent(path_from_cstr("ab")).buffer, ".");
  assert_cstr_eq(path_parent(path_from_cstr("a")).buffer, ".");
  assert_cstr_eq(path_parent(path_from_cstr("../../..")).buffer, "../..");
  // root has no directory
  assert_cstr_eq(path_parent(path_from_cstr("/")).buffer, "/");
  // Like with posix `dirname`: Strings cotnaining no slash are always in the current directory
  assert_cstr_eq(path_parent(path_from_cstr(".")).buffer, ".");
  assert_cstr_eq(path_parent(path_from_cstr("..")).buffer, ".");
  

  // ==== path_is_c_file ====
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
