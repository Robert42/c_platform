// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

usize MEM_PAGE_SIZE = 0;

u8* mem_page_reserve(usize num_bytes)
{
  debug_assert_usize_gt(num_bytes, 0);
  debug_assert(mem_page_is_aligned_usize(num_bytes));

  void* addr = mmap(NULL, num_bytes, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
  LINUX_ASSERT_NE(addr, MAP_FAILED);

  return (u8*)addr;
}

void mem_page_free(u8* addr_begin, usize num_bytes)
{
  debug_assert(mem_page_is_aligned_ptr(addr_begin));
  debug_assert(mem_page_is_aligned_usize(num_bytes));
  debug_assert_ptr_ne(addr_begin, NULL);

  LINUX_ASSERT_EQ(munmap(addr_begin, num_bytes), 0);
}

void mem_page_commit(u8* addr_begin, usize num_bytes)
{
  debug_assert(mem_page_is_aligned_ptr(addr_begin));
  debug_assert(mem_page_is_aligned_usize(num_bytes));
  debug_assert_ptr_ne(addr_begin, NULL);

  LINUX_ASSERT_EQ(mprotect(addr_begin, num_bytes, PROT_READ|PROT_WRITE), 0);
}

void mem_page_uncommit(u8* addr_begin, usize num_bytes)
{
  debug_assert(mem_page_is_aligned_ptr(addr_begin));
  debug_assert(mem_page_is_aligned_usize(num_bytes));
  debug_assert_ptr_ne(addr_begin, NULL);

  void* addr = mmap(addr_begin, num_bytes, PROT_NONE, MAP_FIXED|MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
  LINUX_ASSERT_EQ(addr, addr_begin);
}

bool mem_page_is_aligned_ptr(const void* ptr)
{
  return mem_page_is_aligned_usize((usize)ptr);
}

void mem_page_init(void)
{
  MEM_PAGE_SIZE = getpagesize();

  // These two assertions together guarantee that no simd value will evver
  // cross the boundary from a valid page to an invalid memory page.
  debug_assert_usize_gte(MEM_PAGE_SIZE, 512/8);
  debug_assert_bool_eq(is_power_of_two_or_zero_usize(MEM_PAGE_SIZE), true);
}
