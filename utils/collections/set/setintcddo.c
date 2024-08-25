// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

// Checks whether a new set is identical to the old one by
//
// Usecase:
// - I need to know, whether a new set is identical to an old set.
// - After that `update`, the old set is not used anymore
// - This check is used multiple times
// - the sets are relative small (less than a few thousands)
//
// Memory layout:
// - A single buffer containin two arrays.
// - The new set is the first array
// - The old set is the second array
// - both arrays are adiescent in memory
// - Whenever an item is inserted to the new set
//   - it is searched in the first ad second array
//   - if it already exists in the first array, nothing needs to be done
//   - if it already exists in the second array, it is moved to the first via
//     swap.
//   - if it does not exists in the second array, the first item of the second
//     array is swapped to the end to make space for the first array adding the
//     new item
// - Each insertion operation returns the information, which action was done
// - After the new set was created, call reset.
//   - The first array becomes the second
//     - No element is moved, simple the length copied and the length of the
//       first array set to zero.
enum Set_Int_Change_Detection_Dismissing_Old_Change
{
  SETINTCDDOC_NEW,
  SETINTCDDOC_OLD,
  SETINTCDDOC_ALREADY_INSERTED,
};
struct Set_Int_Change_Detection_Dismissing_Old
{
  int xs[4096];
  u16 len_new;
  u16 len_old;
};
static void setintcddo_reset(struct Set_Int_Change_Detection_Dismissing_Old* set);
static enum Set_Int_Change_Detection_Dismissing_Old_Change setintcddo_insert(struct Set_Int_Change_Detection_Dismissing_Old* set, int value);


static void setintcddo_reset(struct Set_Int_Change_Detection_Dismissing_Old* set)
{
  set->len_old = set->len_new;
  set->len_new = 0;
}
static enum Set_Int_Change_Detection_Dismissing_Old_Change setintcddo_insert(struct Set_Int_Change_Detection_Dismissing_Old* set, int value)
{
  for(usize i=0; i<set->len_new; ++i)
    if(set->xs[i] == value)
      return SETINTCDDOC_ALREADY_INSERTED;

  const usize begin = set->len_new;
  const usize end = begin + set->len_old;
  for(usize i=begin; i<end; ++i)
    if(set->xs[i] == value)
    {
      // swap `set->xs[set->len_new]` with `set->xs[i]` (which is `value`)
      set->xs[i] = set->xs[set->len_new];
      set->xs[set->len_new] = value;

      set->len_new++;
      set->len_old--;
      return SETINTCDDOC_OLD;
    }

  debug_assert_usize_lt(end, ARRAY_LEN(set->xs)); // buffer too small!
  // make space for new value
  set->xs[end] = set->xs[set->len_new];
  set->xs[set->len_new++] = value;
  return SETINTCDDOC_NEW;
}
