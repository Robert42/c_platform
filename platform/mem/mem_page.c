// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

bool mem_page_is_aligned_usize(usize x)
{
  // MEM_PAGE_SIZE is a power of two and the compiler doesn't know it
  const usize result = (x & (MEM_PAGE_SIZE-1)) == 0;

  debug_assert_bool_eq(x % MEM_PAGE_SIZE == 0, result);

  return result;
}

usize mem_page_ceil_multiple_usize(usize x)
{
  return ceil_multiple_of_power_of_two_usize(x, MEM_PAGE_SIZE);
}
