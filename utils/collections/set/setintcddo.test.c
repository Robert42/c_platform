// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "setintcddo.c"

void setintcddo_test()
{
  struct Set_Int_Change_Detection_Dismissing_Old xs = {};
  debug_assert_usize_eq(xs.len_new, 0);
  debug_assert_usize_eq(xs.len_old, 0);

  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_NEW);
  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_usize_eq(xs.len_new, 1);
  debug_assert_usize_eq(xs.len_old, 0);

  debug_assert_int_eq(setintcddo_insert(&xs, 37), SETINTCDDOC_NEW);
  debug_assert_usize_eq(xs.len_new, 2);
  debug_assert_usize_eq(xs.len_old, 0);
  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 37), SETINTCDDOC_ALREADY_INSERTED);

  setintcddo_reset(&xs);
  debug_assert_usize_eq(xs.len_new, 0);
  debug_assert_usize_eq(xs.len_old, 2);

  debug_assert_int_eq(setintcddo_insert(&xs, 137), SETINTCDDOC_NEW);
  debug_assert_int_eq(setintcddo_insert(&xs, 137), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_usize_eq(xs.len_new, 1);
  debug_assert_usize_eq(xs.len_old, 2);

  debug_assert_int_eq(setintcddo_insert(&xs, 37), SETINTCDDOC_OLD);
  debug_assert_int_eq(setintcddo_insert(&xs, 137), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 37), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_usize_eq(xs.len_new, 2);
  debug_assert_usize_eq(xs.len_old, 1);

  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_OLD);
  debug_assert_int_eq(setintcddo_insert(&xs, 137), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 37), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_usize_eq(xs.len_new, 3);
  debug_assert_usize_eq(xs.len_old, 0);
}
