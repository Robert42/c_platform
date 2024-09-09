// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

usize MEM_PAGE_SIZE = 0;

void mem_page_init(void)
{
  MEM_PAGE_SIZE = getpagesize();
}
