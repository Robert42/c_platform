// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "str.h"

void str_test()
{
  // str_from_cstr_slice
  {
    const char src[] = "Let me say: Hello, World";
    const str s = str_from_cstr_len(src+12, 5);

    assert_ptr_eq(s.begin, src+12);
    assert_ptr_eq(s.end, src+12+5);
    assert_usize_eq(str_len(s), 5);
    assert_str_eq(s, STR_LIT("Hello"));
    
    const str empty = str_from_cstr_len(src+3, 0);
    assert_ptr_eq(empty.begin, src+3);
    assert_ptr_eq(empty.end, empty.begin);
    assert_usize_eq(str_len(empty), 0);
    assert_str_eq(empty, STR_LIT(""));
    
    const str src_as_str = STR_LIT(src);
    assert_usize_eq(str_len(src_as_str), 24);
    assert_ptr_eq(src_as_str.begin, src);
    assert_ptr_eq(src_as_str.end, src+24);
    assert_usize_eq(src_as_str.end[-5], 'W');
    assert_usize_eq(src_as_str.end[-4], 'o');
    assert_usize_eq(src_as_str.end[-3], 'r');
    assert_usize_eq(src_as_str.end[-2], 'l');
    assert_usize_eq(src_as_str.end[-1], 'd');
    assert_str_eq(src_as_str, STR_LIT("Let me say: Hello, World"));
  }

  // str_cmp
  {
    // empty
    assert_int_eq(str_cmp(STR_LIT(""), STR_LIT("")), 0);

    // difference in the content
    assert_int_lt(str_cmp(STR_LIT("x"), STR_LIT("y")), 0);
    assert_int_gt(str_cmp(STR_LIT("z"), STR_LIT("y")), 0);
    assert_int_lt(str_cmp(STR_LIT("xyz"), STR_LIT("xzz")), 0);
    assert_int_gt(str_cmp(STR_LIT("xyz"), STR_LIT("xyy")), 0);

    // difference in the length
    assert_int_gt(str_cmp(STR_LIT("x"), STR_LIT("")), 0);
    assert_int_lt(str_cmp(STR_LIT(""), STR_LIT("x")), 0);
    assert_int_lt(str_cmp(STR_LIT("xy"), STR_LIT("xyz")), 0);
    assert_int_lt(str_cmp(STR_LIT("xy"), STR_LIT("xya")), 0);
    assert_int_gt(str_cmp(STR_LIT("xyz"), STR_LIT("xy")), 0);
    assert_int_gt(str_cmp(STR_LIT("xya"), STR_LIT("xy")), 0);
    
    const char src[] = "xyzuvw";
    assert_int_gt(str_cmp(str_from_cstr_len(src, 3), str_from_cstr_len(src, 2)), 0);
  }

  // str_cstr_cmp
  {
    assert_int_eq(str_cstr_cmp(STR_LIT(""), ""), 0);
    assert_int_lt(str_cstr_cmp(STR_LIT(""), "x"), 0);
    assert_int_lt(str_cstr_cmp(STR_LIT("\0"), "x"), 0);
    assert_int_gt(str_cstr_cmp(STR_LIT("\0"), ""), 0);
    assert_int_gt(str_cstr_cmp(STR_LIT("x\0z"), "x"), 0);
    assert_int_gt(str_cstr_cmp(STR_LIT("x"), ""), 0);
    assert_int_lt(str_cstr_cmp(STR_LIT(""), "xyz"), 0);
    assert_int_gt(str_cstr_cmp(STR_LIT("xyz"), ""), 0);

    assert_int_eq(str_cstr_cmp(STR_LIT("x"), "x"), 0);
    assert_int_eq(str_cstr_cmp(STR_LIT("xyz"), "xyz"), 0);
    assert_int_lt(str_cstr_cmp(STR_LIT("xyy"), "xyz"), 0);
    assert_int_gt(str_cstr_cmp(STR_LIT("xzz"), "xyz"), 0);
  }

  {
    assert_cstr_eq(str_fmt(STR_LIT("xyz")), "xyz");
  }
  
  // cstr_fmt
  {
    u8 BUFFER[4096];
    Mem_Region region = MEM_REGION_FROM_ARRAY(BUFFER);
    
    assert_cstr_eq(cstr_fmt(&region, "Hello, %s!", "World"), "Hello, World!");
  }

  // str_trim_right
  {
    assert_str_eq(str_trim_right(STR_LIT("")), STR_LIT(""));
    assert_str_eq(str_trim_right(STR_LIT("  \n  \t  ")), STR_LIT(""));
    assert_str_eq(str_trim_right(STR_LIT("xyz")), STR_LIT("xyz"));
    assert_str_eq(str_trim_right(STR_LIT("xyz  \n  \t  ")), STR_LIT("xyz"));
  }

  // str_ends_with
  {
    assert_bool_eq(str_ends_with(STR_LIT(""), STR_LIT("")), true);
    assert_bool_eq(str_ends_with(STR_LIT("x"), STR_LIT("")), true);
    assert_bool_eq(str_ends_with(STR_LIT("x"), STR_LIT("x")), true);
    assert_bool_eq(str_ends_with(STR_LIT("x"), STR_LIT("y")), false);
    assert_bool_eq(str_ends_with(STR_LIT("xy"), STR_LIT("x")), false);
    assert_bool_eq(str_ends_with(STR_LIT("yx"), STR_LIT("x")), true);
    assert_bool_eq(str_ends_with(STR_LIT("x"), STR_LIT("xx")), false);
  }
}
