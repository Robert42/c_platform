// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "dev/env.h"

#if ENV_COMPILER == COMPILER_TCC

typedef _Bool bool;
#define true ((bool)1)
#define false ((bool)0)

void abort();

#include <tcclib.h>

#ifdef __linux__

#define STDIN_FILENO 0
#define STDOUT_FILENO 1
#define STDERR_FILENO 2

int isatty(int fd);

#endif // __linux__

#else // ENV_COMPILER == COMPILER_TCC

#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#endif // ENV_COMPILER == COMPILER_TCC
