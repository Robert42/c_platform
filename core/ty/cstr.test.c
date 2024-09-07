// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

void cstr_test()
{
  // empty string => do nothing
  {
    char xs[1] = {0};
    cstr_trim_right(xs);
    assert_cstr_eq(xs, "");
  }

  // string consinsting only out of whitespace => empty string
  {
    char xs[] = "\n";
    cstr_trim_right(xs);
    assert_cstr_eq(xs, "");
  }

  // string with content vefore the whitespace
  {
    char xs[] = "xyz\n";
    cstr_trim_right(xs);
    assert_cstr_eq(xs, "xyz");
  }

  // recognize newlines, tabs and regular spaces as whitespace
  {
    char xs[] = "xyz\n";
    cstr_trim_right(xs);
    assert_cstr_eq(xs, "xyz");
  }
}
