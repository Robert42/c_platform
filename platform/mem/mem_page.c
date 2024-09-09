// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

bool is_multiple_of_pagesize(usize x)
{
  // MEM_PAGE_SIZE is a power of two and the compiler doesn't know it
  const usize result = (x & (MEM_PAGE_SIZE-1)) == 0;

  debug_assert_bool_eq(x % MEM_PAGE_SIZE == 0, result);

  return result;
}

