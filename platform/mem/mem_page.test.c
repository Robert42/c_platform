// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

void mem_page_test()
{
  // is_multiple_of_pagesize
  {
    assert_bool_eq(is_multiple_of_pagesize(1), false);
    assert_bool_eq(is_multiple_of_pagesize(MEM_PAGE_SIZE), true);
    assert_bool_eq(is_multiple_of_pagesize(MEM_PAGE_SIZE+1), false);
    assert_bool_eq(is_multiple_of_pagesize(2*MEM_PAGE_SIZE-1), false);
    assert_bool_eq(is_multiple_of_pagesize(2*MEM_PAGE_SIZE), true);
    assert_bool_eq(is_multiple_of_pagesize(2*MEM_PAGE_SIZE+1), false);
  }

  // ceil_multiple_of_pagesize
  {
    assert_usize_eq(ceil_multiple_of_pagesize(0), 0);
    assert_usize_eq(ceil_multiple_of_pagesize(1), MEM_PAGE_SIZE);
    assert_usize_eq(ceil_multiple_of_pagesize(2), MEM_PAGE_SIZE);
    assert_usize_eq(ceil_multiple_of_pagesize(MEM_PAGE_SIZE-1), MEM_PAGE_SIZE);
    assert_usize_eq(ceil_multiple_of_pagesize(MEM_PAGE_SIZE), MEM_PAGE_SIZE);
    assert_usize_eq(ceil_multiple_of_pagesize(MEM_PAGE_SIZE+1), 2*MEM_PAGE_SIZE);
    assert_usize_eq(ceil_multiple_of_pagesize(MEM_PAGE_SIZE+2), 2*MEM_PAGE_SIZE);
  }

  {
    const usize size = 4*MEM_PAGE_SIZE;
    u8* pages_begin = mem_page_reserve(size);
    // pages_begin[0] = 42; // would crash

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
