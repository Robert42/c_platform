// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "setintcddo.c"

void setintcddo_test()
{
  struct Set_Int_Change_Detection_Dismissing_Old xs = {0};
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

  setintcddo_reset(&xs);
  debug_assert_usize_eq(xs.len_new, 0);
  debug_assert_usize_eq(xs.len_old, 3);

  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_OLD);
  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_usize_eq(xs.len_new, 1);
  debug_assert_usize_eq(xs.len_old, 2);

  debug_assert_int_eq(setintcddo_insert(&xs, 123), SETINTCDDOC_NEW);
  debug_assert_int_eq(setintcddo_insert(&xs, 123), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_usize_eq(xs.len_new, 2);
  debug_assert_usize_eq(xs.len_old, 2);

  debug_assert_int_eq(setintcddo_insert(&xs, 37), SETINTCDDOC_OLD);
  debug_assert_int_eq(setintcddo_insert(&xs, 123), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 37), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_usize_eq(xs.len_new, 3);
  debug_assert_usize_eq(xs.len_old, 1);

  debug_assert_int_eq(setintcddo_insert(&xs, 1337), SETINTCDDOC_NEW);
  debug_assert_int_eq(setintcddo_insert(&xs, 123), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 37), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 1337), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_usize_eq(xs.len_new, 4);
  debug_assert_usize_eq(xs.len_old, 1);

  debug_assert_int_eq(setintcddo_insert(&xs, 137), SETINTCDDOC_OLD);
  debug_assert_int_eq(setintcddo_insert(&xs, 123), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 37), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 1337), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 137), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_usize_eq(xs.len_new, 5);
  debug_assert_usize_eq(xs.len_old, 0);

  // Remove entries, again
  debug_assert_bool_eq(setintcddo_remove(&xs, 42), true);
  debug_assert_usize_eq(xs.len_new, 4);
  debug_assert_usize_eq(xs.len_old, 1);
  debug_assert_bool_eq(setintcddo_remove(&xs, 42), false);
  debug_assert_usize_eq(xs.len_new, 4);
  debug_assert_usize_eq(xs.len_old, 1);
  debug_assert_int_eq(setintcddo_insert(&xs, 123), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 37), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 1337), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 137), SETINTCDDOC_ALREADY_INSERTED);
  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_OLD);
}
