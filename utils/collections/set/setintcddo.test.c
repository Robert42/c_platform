// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "setintcddo.c"

void setintcddo_test()
{
  struct Set_Int_Change_Detection_Dismissing_Old xs = {};

  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_NEW);
  debug_assert_int_eq(setintcddo_insert(&xs, 42), SETINTCDDOC_ALREADY_INSERTED);
}
