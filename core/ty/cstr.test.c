// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

void cstr_test()
{
  const Mem_Region _prev = STACK;

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

  // trim multiple chars
  {
    char xs[] = "xyz\n\n\n\n\n";
    cstr_trim_right(xs);
    assert_cstr_eq(xs, "xyz");
  }

  // recognize newlines, tabs and regular spaces as whitespace
  {
    char xs[] = "xyz\n\t \n\t ";
    cstr_trim_right(xs);
    assert_cstr_eq(xs, "xyz");
  }

#define MIXED " !.\n?@ABYZ[\\_`abyz{|}~"
#define UPPER " !.\n?@ABYZ[\\_`ABYZ{|}~"
#define LOWER " !.\n?@abyz[\\_`abyz{|}~"
  {
    char xs[] = MIXED;
    convert_cstr_to_lower(xs);
    assert_cstr_eq(xs, LOWER);
    assert_cstr_eq(cstr_to_lower(&STACK, MIXED), LOWER);
  }
  {
    char xs[] = MIXED;
    convert_cstr_to_upper(xs);
    assert_cstr_eq(xs, UPPER);
    assert_cstr_eq(cstr_to_upper(&STACK, MIXED), UPPER);
  }
#undef MIXED
#undef UPPER
#undef LOWER

  STACK = _prev;
}
