// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#define NORETURN __attribute__((noreturn))
#define UNUSED __attribute__((unused))

#define ATT_PRINTF(FORMAT_CSTR, FIRST_ARG_TO_CHECK) __attribute((format(printf, FORMAT_CSTR, FIRST_ARG_TO_CHECK)))

// TODO use intrinsic
#define LIKELY(X) X
