// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

BIN_ASSERT_NUM_CMP(usize, usize)
BIN_ASSERT_NUM_CMP(ssize, ssize)
BIN_ASSERT_NUM_CMP(int, int)
BIN_ASSERT_NUM_CMP(ptr, const void*)
BIN_ASSERT_CUSTOM(cstr_eq, const char*, (strcmp(x,y)==0), )
BIN_ASSERT_CUSTOM(bool_eq, bool, x==y, fmt_bool)
RNG_ASSERT_NUM_CMP(usize, usize)
RNG_ASSERT_NUM_CMP(ssize, ssize)
RNG_ASSERT_NUM_CMP(ptr, const void*)

/*@
  terminates true;
  assigns \nothing;
  exits false;
  admit ensures x <= y;
*/
void assert_usize_lte(usize x, usize y);

/*@
  terminates true;
  assigns \nothing;
  exits false;
  admit ensures x < y;
*/
void assert_usize_lt(usize x, usize y);

/*@
  terminates true;
  assigns \nothing;
  exits false;
  admit ensures x <= y;
*/
void assert_ssize_lte(ssize x, ssize y);
/*@
  terminates true;
  assigns \nothing;
  exits false;
  admit ensures x <= y < z;
*/
void assert_usize_lte_lt(usize x, usize y, usize z);

