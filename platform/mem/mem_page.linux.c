// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

usize MEM_PAGE_SIZE = 0;

void mem_page_init(void)
{
  MEM_PAGE_SIZE = getpagesize();

  // These two assertions together guarantee that no simd value will evver
  // cross the boundary from a valid page to an invalid memory page.
  debug_assert_usize_gte(MEM_PAGE_SIZE, 512/8);
  debug_assert_bool_eq(is_power_of_two_or_zero_usize(MEM_PAGE_SIZE), true);
}
