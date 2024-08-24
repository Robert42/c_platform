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

#include <sys/types.h> // pid_t

#define STDIN_FILENO 0
#define STDOUT_FILENO 1
#define STDERR_FILENO 2

int isatty(int fd);
int close(int fd);
pid_t fork(void);
int execvp(const char* file, char* const argv[]);
int execvpe(const char* file, char* const argv[], char* const env[]);
int waitpid(pid_t pid, int* status, int options);
int dup2(int oldfd, int newfd);
ssize_t read(int fd, void* buffer, size_t num_bytes);

// NOT portable! Works on x86 and and aarch64
// TODO: replace with portable `pipe2`
int pipe(int pipefd[2]);

int strcmp(const char* x, const char* y);
const char* dirname(const char* path);

#endif // __linux__

#else // ENV_COMPILER == COMPILER_TCC

#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <libgen.h>
#include <sys/wait.h> // waitpid

#include <string.h>

#endif // ENV_COMPILER == COMPILER_TCC

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

