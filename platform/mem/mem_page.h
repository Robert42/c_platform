// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

extern usize MEM_PAGE_SIZE;

void mem_page_init(void);

bool is_multiple_of_pagesize(usize x);
usize ceil_multiple_of_pagesize(usize x);

