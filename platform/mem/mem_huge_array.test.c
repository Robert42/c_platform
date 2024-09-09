// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

static const char* _huge_array_commit_fmt(struct Huge_Array_Commit x)
{
  return cstr_fmt(&PANIC_REGION, "(struct Huge_Array_Commit)\n{\n  .commit_begin = %p,\n  .num_bytes = %zu,\n}\n", x.commit_begin, x.num_bytes);
}
static void __assert_huge_array_commit_eq__(struct Huge_Array_Commit x, struct Huge_Array_Commit y, const char* condition, const char* file, int line)
{
  if(LIKELY(x.commit_begin == y.commit_begin && x.num_bytes == y.num_bytes))
    return;
  const char* lhs = _huge_array_commit_fmt(x);
  const char* rhs = _huge_array_commit_fmt(y);
  __bin_assert_failed__(condition, lhs, rhs, file, line);
}
#define assert_huge_array_commit_eq(X, Y) __assert_huge_array_commit_eq__((X), (Y), #X " == " #Y, __FILE__, __LINE__)

void mem_huge_array_test()
{
  const usize _real_page_size = MEM_PAGE_SIZE;
  MEM_PAGE_SIZE = 1024;

  u8* const block_begin = (u8*)(1024*1024);

  const struct Huge_Array_Meta_Data meta_data = {
    .max_capacity = 500,
    .item_size = 24,
    .item_alignment = 8,
  };
  
  struct Huge_Array huge_array = {
    .block_begin = block_begin,
    .capacity = 0,
#if ENV_DEBUG
    .meta_data = meta_data,
#endif
  };

  // not increasing capacity ==> nothing to do
  assert_huge_array_commit_eq(
    _huge_array_calc_addr_range_to_commit(0, huge_array, meta_data),
    ((struct Huge_Array_Commit){.commit_begin = block_begin+0, .num_bytes=0})
  );

  // not allocating one item ==> commit to one memory page
  assert_huge_array_commit_eq(
    _huge_array_calc_addr_range_to_commit(1, huge_array, meta_data),
    ((struct Huge_Array_Commit){.commit_begin = block_begin+0, .num_bytes=1024})
  );
  huge_array.capacity = 1;

  // not increasing capacity ==> nothing to do
  assert_huge_array_commit_eq(
    _huge_array_calc_addr_range_to_commit(1, huge_array, meta_data),
    ((struct Huge_Array_Commit){.commit_begin = block_begin+0, .num_bytes=0})
  );

  // increasing but still within same memory page ==> nothing to do
  assert_huge_array_commit_eq(
    _huge_array_calc_addr_range_to_commit(2, huge_array, meta_data),
    ((struct Huge_Array_Commit){.commit_begin = block_begin+1024, .num_bytes=0})
  );
  huge_array.capacity = 2;

  // increasing but still within same memory page ==> nothing to do
  assert_huge_array_commit_eq(
    _huge_array_calc_addr_range_to_commit(42, huge_array, meta_data),
    ((struct Huge_Array_Commit){.commit_begin = block_begin+1024, .num_bytes=0})
  );
  huge_array.capacity = 42;

  // not increasing capacity ==> nothing to do
  assert_huge_array_commit_eq(
    _huge_array_calc_addr_range_to_commit(37, huge_array, meta_data),
    ((struct Huge_Array_Commit){.commit_begin = block_begin+0, .num_bytes=0})
  );

  // increasing exceeding memory page ==> allocate one more page
  assert_huge_array_commit_eq(
    _huge_array_calc_addr_range_to_commit(43, huge_array, meta_data),
    ((struct Huge_Array_Commit){.commit_begin = block_begin+1024, .num_bytes=1024})
  );
  huge_array.capacity = 43;

  // increasing exceeding memory page ==> allocate one more page
  assert_huge_array_commit_eq(
    _huge_array_calc_addr_range_to_commit(200, huge_array, meta_data),
    ((struct Huge_Array_Commit){.commit_begin = block_begin+2048, .num_bytes=3072})
  );
  huge_array.capacity = 43;

  MEM_PAGE_SIZE = _real_page_size; // restore the real memory page size
}
