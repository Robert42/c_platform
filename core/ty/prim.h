// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#if ENV_COMPILER == COMPILER_TCC

typedef _Bool bool;
#define true ((bool)1)
#define false ((bool)0)

#include <tcclib.h>

#elif ENV_COMPILER == COMPILER_FRAMAC

#include <stdbool.h>
#include <stdint.h>
#include <__fc_define_ssize_t.h>
#include <__fc_define_size_t.h>

#else // gcc/clang/...

#if ENV_COMPILER == COMPILER_GCC || ENV_COMPILER == COMPILER_CLANG
#define _GNU_SOURCE
#endif

#include <stdbool.h>
#include <stdlib.h>
#include <stdint.h>
#include <stddef.h>

#endif

#include <inttypes.h>

typedef uint8_t u8;
typedef  int8_t s8;
typedef uint16_t u16;
typedef  int16_t s16;
typedef uint32_t u32;
typedef  int32_t s32;
typedef uint64_t u64;
typedef  int64_t s64;
typedef size_t usize;
typedef ssize_t ssize;

