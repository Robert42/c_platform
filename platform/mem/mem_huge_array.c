// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

struct Huge_Array huge_array_reserve(struct Huge_Array_Meta_Data meta_data)
{
  debug_assert(is_multiple_of_power_of_two_usize(meta_data.item_size, meta_data.item_alignment));
  TODO();
}

struct Huge_Array huge_array_capacity_commit(usize new_capacity, struct Huge_Array array, struct Huge_Array_Meta_Data meta_data)
{
  TODO();
}

struct Huge_Array_Commit _huge_array_calc_addr_range_to_commit(usize new_capacity, struct Huge_Array array, struct Huge_Array_Meta_Data meta_data)
{
  debug_assert_usize_eq(array.meta_data.max_capacity, meta_data.max_capacity);
  debug_assert_usize_eq(array.meta_data.item_size, meta_data.item_size);
  debug_assert_usize_eq(array.meta_data.item_alignment, meta_data.item_alignment);

  if(LIKELY(new_capacity <= array.capacity))
    return (struct Huge_Array_Commit){.commit_begin = array.block_begin, .num_bytes = 0};

  assert_usize_lte(new_capacity, meta_data.max_capacity);

  const usize old_offset = mem_page_ceil_multiple_usize(array.capacity * meta_data.item_size);
  const usize new_offset = mem_page_ceil_multiple_usize(new_capacity * meta_data.item_size);

  return (struct Huge_Array_Commit){
    .commit_begin = array.block_begin + old_offset,
    .num_bytes = new_offset - old_offset,
  };
}


struct Huge_Array_Meta_Data _new_huge_array_metadata(usize max_capacity, usize item_size, usize item_alignment)
{
  const struct Huge_Array_Meta_Data meta_data = {
    .max_capacity = max_capacity,
    .item_size = item_size,
    .item_alignment = item_alignment,
  };

  // I don't half the nyumber of bits to store the item_size and item_alignment.
  // Check, whether information was lost because of that.
  debug_assert(meta_data.item_size == item_size);
  debug_assert(meta_data.item_alignment == item_alignment);

  return meta_data;
}
