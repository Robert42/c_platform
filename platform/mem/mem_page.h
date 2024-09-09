// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

extern usize MEM_PAGE_SIZE;

u8* mem_page_reserve(usize num_bytes);
void mem_page_free(u8* addr_begin, usize num_bytes);
void mem_page_commit(u8* addr_begin, usize num_bytes);
void mem_page_uncommit(u8* addr_begin, usize num_bytes);

void mem_page_init(void);

bool mem_page_is_aligned_ptr(const void* ptr);
bool mem_page_is_aligned_usize(usize x);
usize mem_page_ceil_multiple_usize(usize x);

// The result is always aligned to alignment.
void* mem_pages_from_pre_reserved(usize num_bytes, usize alignment);
