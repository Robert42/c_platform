// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
u8* mem_page_reserve(usize num_bytes)
{
  debug_assert_usize_gt(num_bytes, 0);
  debug_assert(is_multiple_of_pagesize(num_bytes));

  void* addr = mmap(NULL, num_bytes, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
  LINUX_ASSERT_NE(addr, MAP_FAILED);

  return (u8*)addr;
}

void mem_page_free(u8* addr_begin, usize num_bytes)
{
  // TODO: add assertion for addr_begin being mem_page alogned
  debug_assert(is_multiple_of_pagesize(num_bytes));
  debug_assert_ptr_ne(addr_begin, NULL);

  LINUX_ASSERT_EQ(munmap(addr_begin, num_bytes), 0);
}

void mem_page_commit(u8* addr_begin, usize num_bytes)
{
  // TODO: add assertion for addr_begin being mem_page alogned
  debug_assert(is_multiple_of_pagesize(num_bytes));
  debug_assert_ptr_ne(addr_begin, NULL);

  LINUX_ASSERT_EQ(mprotect(addr_begin, num_bytes, PROT_READ|PROT_WRITE), 0);
}

void mem_page_uncommit(u8* addr_begin, usize num_bytes)
{
  // TODO: add assertion for addr_begin being mem_page alogned
  debug_assert(is_multiple_of_pagesize(num_bytes));
  debug_assert_ptr_ne(addr_begin, NULL);

  void* addr = mmap(addr_begin, num_bytes, PROT_NONE, MAP_FIXED|MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
  LINUX_ASSERT_EQ(addr, addr_begin);
}

bool is_multiple_of_pagesize(usize x)
{
  // MEM_PAGE_SIZE is a power of two and the compiler doesn't know it
  const usize result = (x & (MEM_PAGE_SIZE-1)) == 0;

  debug_assert_bool_eq(x % MEM_PAGE_SIZE == 0, result);

  return result;
}

usize ceil_multiple_of_pagesize(usize x)
{
  const usize nonzero_bits = x & (MEM_PAGE_SIZE-1);
  const usize missing_to_next = 1 + (~nonzero_bits & (MEM_PAGE_SIZE-1));
  const usize result = nonzero_bits ? x + missing_to_next : x;
  debug_assert_bool_eq(ceil_multiple_of(x, MEM_PAGE_SIZE), result);

  return result;
}
