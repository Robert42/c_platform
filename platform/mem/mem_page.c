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
  const usize nonzero_bits = x & (MEM_PAGE_SIZE-1);
  const usize missing_to_next = 1 + (~nonzero_bits & (MEM_PAGE_SIZE-1));
  const usize result = nonzero_bits ? x + missing_to_next : x;
  debug_assert_bool_eq(ceil_multiple_of(x, MEM_PAGE_SIZE), result);

  return result;
}
