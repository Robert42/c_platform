// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "c_tok.h"

inline static char* test_c_tok_parse_str_lit(const char* code, const char* expected_rest)
{
  Mem_Region* region = &SCRATCH;

  const char* const begin = (char*)mem_region_copy_to_region(region, code, strlen(code), 1);
  const char* const end = (char*)mem_region_copy_to_region(region, expected_rest, strlen(expected_rest), 1);

  const char* rest = begin;
  char* parsed_result = c_tok_parse_str_lit(region, &rest);

  assert_ptr_eq(rest, end);

  return parsed_result;
}

static const char* c_tok_fmt_list_str_test(const char* content)
{
  Fmt f = fmt_new_from_region(&SCRATCH, 1024);
  c_tok_fmt_cstr_lit(&f, content);
  return f.begin;
}

void c_tok_test()
{
  assert_cstr_eq(test_c_tok_parse_str_lit("\"\"", ","), "");
  assert_cstr_eq(test_c_tok_parse_str_lit("\"x\"", ","), "x");
  assert_cstr_eq(test_c_tok_parse_str_lit("\"xyz\"", ""), "xyz");
  assert_cstr_eq(test_c_tok_parse_str_lit("\"x y z\"", "\n"), "x y z");
  assert_cstr_eq(test_c_tok_parse_str_lit("\" \\\" \"", "\n"), " \" ");
  assert_cstr_eq(test_c_tok_parse_str_lit("\" \\\\ \"", "\n"), " \\ ");
  assert_cstr_eq(test_c_tok_parse_str_lit("\" \\n \"", "\n"), " \n ");

  assert_cstr_eq(c_tok_fmt_list_str_test(""), "\"\"");
  assert_cstr_eq(c_tok_fmt_list_str_test("xyz \n  "), "\"xyz \\n  \"");
  assert_cstr_eq(c_tok_fmt_list_str_test("\""), "\"\\\"\"");
  assert_cstr_eq(c_tok_fmt_list_str_test("\\"), "\"\\\\\"");

  {
    Fmt f = fmt_new_from_region(&SCRATCH, 16);

    str xs = str_from_cstr("xyz");
    xs.end--;
    c_tok_fmt_str_lit(&f, xs);
    assert_cstr_eq(f.begin, "\"xy\"");
  }
}
