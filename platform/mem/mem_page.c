// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

bool mem_page_is_aligned_ptr(const void* ptr)
{
  return mem_page_is_aligned_usize((usize)ptr);
}

bool mem_page_is_aligned_usize(usize x)
{
  return is_multiple_of_power_of_two_usize(x, MEM_PAGE_SIZE);
}

usize mem_page_ceil_multiple_usize(usize x)
{
  return ceil_multiple_of_power_of_two_usize(x, MEM_PAGE_SIZE);
}

usize _mem_page_init_get_page_size(void);
void mem_page_init()
{
  MEM_PAGE_SIZE = getpagesize();

  // These two assertions together guarantee that no simd value will evver
  // cross the boundary from a valid page to an invalid memory page.
  debug_assert_usize_gte(MEM_PAGE_SIZE, 512/8);
  debug_assert_bool_eq(is_power_of_two_or_zero_usize(MEM_PAGE_SIZE), true);
}
