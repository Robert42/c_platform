// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

usize bytes_mut_len(Bytes_Mut xs)
{
  debug_assert_ptr_lte(xs.begin, xs.end);
  const ssize len = xs.end - xs.begin;
  //@assert len >= 0;
  return len;
}
