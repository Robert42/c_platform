// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

/*@
  terminates true;
  assigns \nothing;
  ensures \result <= x;
  ensures \result <= y;
  ensures \result==x || \result==y;
  exits false;
*/
usize min_usize(usize x, usize y);
