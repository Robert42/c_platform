// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

void mem_page_test()
{
  // mem_page_is_aligned_usize
  {
    assert_bool_eq(mem_page_is_aligned_usize(1), false);
    assert_bool_eq(mem_page_is_aligned_usize(MEM_PAGE_SIZE), true);
    assert_bool_eq(mem_page_is_aligned_usize(MEM_PAGE_SIZE+1), false);
    assert_bool_eq(mem_page_is_aligned_usize(2*MEM_PAGE_SIZE-1), false);
    assert_bool_eq(mem_page_is_aligned_usize(2*MEM_PAGE_SIZE), true);
    assert_bool_eq(mem_page_is_aligned_usize(2*MEM_PAGE_SIZE+1), false);
  }

  // mem_page_ceil_multiple_usize
  {
    assert_usize_eq(mem_page_ceil_multiple_usize(0), 0);
    assert_usize_eq(mem_page_ceil_multiple_usize(1), MEM_PAGE_SIZE);
    assert_usize_eq(mem_page_ceil_multiple_usize(2), MEM_PAGE_SIZE);
    assert_usize_eq(mem_page_ceil_multiple_usize(MEM_PAGE_SIZE-1), MEM_PAGE_SIZE);
    assert_usize_eq(mem_page_ceil_multiple_usize(MEM_PAGE_SIZE), MEM_PAGE_SIZE);
    assert_usize_eq(mem_page_ceil_multiple_usize(MEM_PAGE_SIZE+1), 2*MEM_PAGE_SIZE);
    assert_usize_eq(mem_page_ceil_multiple_usize(MEM_PAGE_SIZE+2), 2*MEM_PAGE_SIZE);
  }

  {
    const usize size = 4*MEM_PAGE_SIZE;
    u8* pages_begin = mem_page_reserve(size);
    // pages_begin[0] = 42; // would crash
    assert(mem_page_is_aligned_ptr(pages_begin));

    mem_page_commit(pages_begin, MEM_PAGE_SIZE);
    pages_begin[0] = 42;
    // pages_begin[MEM_PAGE_SIZE] = 42; // would crash
    
    mem_page_uncommit(pages_begin, 2*MEM_PAGE_SIZE);
    // pages_begin[0] = 42; // would crash
    
    mem_page_commit(pages_begin, MEM_PAGE_SIZE);
    assert_usize_eq(pages_begin[0], 0);
    
    mem_page_free(pages_begin, size);
    // pages_begin[0] = 42; // would crash
  }
}
