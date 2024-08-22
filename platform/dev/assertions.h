// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

BIN_ASSERT_NUM_CMP(usize, usize)
BIN_ASSERT_NUM_CMP(ptr, const void*)
BIN_ASSERT_CUSTOM(cstr_eq, const char*, (strcmp(x,y)==0))

