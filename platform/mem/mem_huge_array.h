// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct Huge_Array_Meta_Data;
struct Huge_Array;
struct Huge_Commit;

struct Huge_Array huge_array_reserve(struct Huge_Array_Meta_Data meta_data);
struct Huge_Array huge_array_capacity_commit(usize new_capacity, struct Huge_Array array, struct Huge_Array_Meta_Data meta_data);

struct Huge_Array_Commit _huge_array_calc_addr_range_to_commit(usize new_capacity, struct Huge_Array array, struct Huge_Array_Meta_Data meta_data); // internal

struct Huge_Array_Meta_Data
{
  usize max_capacity;
  usize item_size : ENV_PTR_BITS/2;
  usize item_alignment : ENV_PTR_BITS/2;
};
struct Huge_Array_Meta_Data _new_huge_array_metadata(usize max_capacity, usize item_size, usize item_alignment);
#define HUGE_ARRAY_META_DATA(TYPE, MAX_CAPACITY) _new_huge_array_metadata((MAX_CAPACITY), sizeof(TYPE), alignof(TYPE))

struct Huge_Array
{
  u8* block_begin;
  usize capacity;
#if ENV_DEBUG
  // Stored for verifying consistency in debug mode
  struct Huge_Array_Meta_Data meta_data;
#endif
};

struct Huge_Array_Commit
{
  u8* commit_begin;
  usize num_bytes;
};


