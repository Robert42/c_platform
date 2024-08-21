// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#ifdef NDEBUG
#define ENV_DEBUG 0
#else
#define ENV_DEBUG 1
#endif

void dev_env_demo();

// ==== assertions ====

void assert_usize_eq(size_t x, size_t y);
void assert_ptr_eq(const void* x, const void* y);
