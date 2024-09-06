// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

/*@
  assigns \nothing;
  ensures \result <= x;
  ensures \result <= y;
  ensures \result==x || \result==y;
*/
usize min_usize(usize x, usize y);
