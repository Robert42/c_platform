// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

void assert_usize_eq(size_t x, size_t y)
{
  if(x != y)
    abort();
}

void assert_ptr_eq(const void* x, const void* y)
{
  if(x != y)
    abort();
}
