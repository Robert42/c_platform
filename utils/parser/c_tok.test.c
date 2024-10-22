// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "c_tok.h"

inline static char* test_c_tok_parse_str_lit(const char* code, const char* expected_rest)
{
  Mem_Region* region = &SCRATCH;

  const char* const begin = (char*)mem_region_copy_to_region(region, code, strlen(code), 1);
  const char* const end = mem_region_copy_to_region(region, expected_rest, strlen(expected_rest), 1);

  const char* rest = begin;
  char* parsed_result = c_tok_parse_str_lit(region, &rest);

  assert_ptr_eq(rest, end);

  return parsed_result;
}

void c_tok_test()
{
  assert_cstr_eq(test_c_tok_parse_str_lit("\"\"", ","), "");
  assert_cstr_eq(test_c_tok_parse_str_lit("\"x\"", ","), "x");
}
