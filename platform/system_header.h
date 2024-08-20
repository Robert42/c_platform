// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

typedef _Bool bool;
#include <tcclib.h>

#ifdef __linux__

#define STDIN_FILENO 0
#define STDOUT_FILENO 1
#define STDERR_FILENO 2

int isatty(int fd);

#endif
