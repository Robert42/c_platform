// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#include "dev/env.h"

#define NORETURN __attribute__((noreturn))

#if ENV_COMPILER == COMPILER_TCC

typedef _Bool bool;
#define true ((bool)1)
#define false ((bool)0)

NORETURN
void abort();

#include <tcclib.h>

#ifdef __linux__

#include <sys/types.h> // pid_t
#include <sys/wait.h> // WIFEXISTED, WEXITSTATUS waitpid
#include <fcntl.h> // openat, O_DIRECTORY

#define STDIN_FILENO 0
#define STDOUT_FILENO 1
#define STDERR_FILENO 2

#define EXIT_SUCCESS 0
#define EXIT_FAILURE 1

int isatty(int fd);
int close(int fd);
pid_t fork(void);
int execvp(const char* file, char* const argv[]);
int execvpe(const char* file, char* const argv[], char* const env[]);
int dup2(int oldfd, int newfd);
ssize_t read(int fd, void* buffer, size_t num_bytes);
int mkdir(const char* path, mode_t mode);

#if ENV_ARCH==ARCH_AARCH64 || ENV_ARCH==ARCH_X86_64 || ENV_ARCH==ARCH_X86_32 || ENV_ARCH==ARCH_X86_16
int pipe(int pipefd[2]);
#endif

int strcmp(const char* x, const char* y);
const char* strstr(const char* haystack, const char* needle);
char* strtok(char* restrict str, const char* restrict delim);
const char* dirname(const char* path);
char* realpath(const char* path, char* buffer);

NORETURN
void errx(int eval, const char* fmt, ...);

#endif // __linux__

#else // ENV_COMPILER == COMPILER_TCC

#if ENV_COMPILER == COMPILER_GCC || ENV_COMPILER == COMPILER_CLANG
#define _GNU_SOURCE
#endif

#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <libgen.h>
#include <fcntl.h>
#include <err.h>
#include <sys/wait.h> // waitpid

#include <string.h>

#endif

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

#ifdef __linux__
#include <time.h>

// source:` man getdents(2)`
struct linux_dirent64
{
  int64_t d_ino;
  int64_t d_off;
  unsigned short d_reclen;
  unsigned char d_type;
  char d_name[];
};
ssize_t getdents64(int fd, void* dirp, size_t count);
#endif
