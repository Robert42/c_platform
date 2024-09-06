// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#if ENV_COMPILER == COMPILER_TCC

typedef _Bool bool;
#define true ((bool)1)
#define false ((bool)0)

#else // ENV_COMPILER == COMPILER_TCC

#include <stdbool.h>

#endif

