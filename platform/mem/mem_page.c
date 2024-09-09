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

Mem_Region _MEM_PAGE_HUGE_PRE_RESERVE_FULL = {0};
Mem_Region _MEM_PAGE_HUGE_PRE_RESERVE_AVAILABLE = {0};

usize _mem_page_init_get_page_size(void);
void mem_page_init()
{
  MEM_PAGE_SIZE = getpagesize();

  // These two assertions together guarantee that no simd value will evver
  // cross the boundary from a valid page to an invalid memory page.
  debug_assert_usize_gte(MEM_PAGE_SIZE, 512/8);
  debug_assert_bool_eq(is_power_of_two_or_zero_usize(MEM_PAGE_SIZE), true);

  const usize huge_pre_reserve = mem_page_ceil_multiple_usize(1 * TiB);
  _MEM_PAGE_HUGE_PRE_RESERVE_FULL = _mem_region_from(mem_page_reserve(huge_pre_reserve), huge_pre_reserve);
  _MEM_PAGE_HUGE_PRE_RESERVE_AVAILABLE = _MEM_PAGE_HUGE_PRE_RESERVE_FULL;
}

void* mem_pages_from_pre_reserved(usize num_bytes, usize alignment)
{
  debug_assert_usize_gt(alignment, 0);
  debug_assert(is_power_of_two_or_zero_usize(alignment));
  // I know no type which has an alignment greater than SIMD vector types (512
  // bits == 64 Bytes) and `mem_page_init()` already asserted that the page
  // size is larger than that.
  // => page boundaries are alraedy aligned to alignment and no further
  // adjustment necessary.
  debug_assert(is_multiple_of_power_of_two_usize(MEM_PAGE_SIZE, alignment));

  num_bytes = mem_page_ceil_multiple_usize(num_bytes);

  void* addr = (void*)mem_region_alloc_bytes_unaligned(&_MEM_PAGE_HUGE_PRE_RESERVE_AVAILABLE, num_bytes);

  debug_assert(mem_page_is_aligned_ptr(addr));
  debug_assert(mem_page_is_aligned_ptr(_MEM_PAGE_HUGE_PRE_RESERVE_AVAILABLE.begin));
  debug_assert(is_multiple_of_power_of_two_usize((usize)addr, alignment));

  return addr;
}
