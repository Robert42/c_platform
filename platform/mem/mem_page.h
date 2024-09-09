// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

extern usize MEM_PAGE_SIZE;

u8* mem_page_reserve(usize num_bytes);
void mem_page_free(u8* addr_begin, usize num_bytes);
void mem_page_commit(u8* addr_begin, usize num_bytes);
void mem_page_uncommit(u8* addr_begin, usize num_bytes);

void mem_page_init(void);

bool is_multiple_of_pagesize(usize x);
usize ceil_multiple_of_pagesize(usize x);

