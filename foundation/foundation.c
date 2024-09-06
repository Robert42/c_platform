// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "prelude.h"

#if ENV_COMPILER == COMPILER_TCC
NORETURN void abort();
#endif

extern Mem_Region PANIC_REGION;

#include "dev/assert.c"
#include "mem/mem.c"
#include "ty/str.c"
#include "fmt.c"

