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
}
