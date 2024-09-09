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
