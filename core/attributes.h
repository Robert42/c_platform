// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#define NORETURN __attribute__((noreturn))
#define UNUSED __attribute__((unused))

#define ATT_PRINTF(FORMAT_CSTR, FIRST_ARG_TO_CHECK) __attribute((format(printf, FORMAT_CSTR, FIRST_ARG_TO_CHECK)))

#if ENV_COMPILER == COMPILER_GCC || ENV_COMPILER == COMPILER_CLANG
#define LIKELY(X) (__builtin_expect((X), 1))
#define UNLIKELY(X) (__builtin_expect((X), 0))
#else
#define LIKELY(X) (X)
#define UNLIKELY(X) (X)
#endif


