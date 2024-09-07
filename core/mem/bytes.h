// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct _platform_io_Bytes_Mut;
typedef struct _platform_io_Bytes_Mut Bytes_Mut;

struct _platform_io_Bytes_Mut
{
  u8* begin;
  u8* end;
};

/*@
  logic integer bytes_mut_len(Bytes_Mut s) = s.end - s.begin;
  predicate bytes_mut_valid(Bytes_Mut s) = 
    s.begin <= s.end &&
    (usize)(s.end - s.begin) == s.end - s.begin &&
    \valid(s.begin + (0 .. bytes_mut_len(s)-1));
*/

/*@
  requires bytes_mut_valid(xs);
  ensures \result == bytes_mut_len(xs);
*/
usize bytes_mut_len(Bytes_Mut xs);
