// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#if ENV_COMPILER == COMPILER_TCC

#ifdef __linux__

#include <sys/types.h> // pid_t
#include <sys/wait.h> // WIFEXISTED, WEXITSTATUS waitpid
#include <sys/stat.h>

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
ssize_t write(int fd, const void* buffer, size_t num_bytes);
int mkdir(const char* path, mode_t mode);
int putenv(const char* env);

#if ENV_ARCH==ARCH_AARCH64 || ENV_ARCH==ARCH_X86_64 || ENV_ARCH==ARCH_X86_32 || ENV_ARCH==ARCH_X86_16
int pipe(int pipefd[2]);
#endif

const char* dirname(const char* path);
char* realpath(const char* path, char* buffer);

int memcmp(const void* s1, const void* s2, size_t n);

int getpagesize(void);

NORETURN
void errx(int eval, const char* fmt, ...);

const char* secure_getenv(const char* name);

#endif // __linux__

int feof(FILE* f);

#else // ENV_COMPILER == COMPILER_TCC

#include <stdio.h>
#include <unistd.h>
#include <libgen.h>
#include <err.h>
#include <sys/wait.h> // waitpid
#include <sys/stat.h> // mkdir

#include <string.h>

#endif

#ifdef __linux__
#include <time.h>
#include <fcntl.h> // openat, O_DIRECTORY
#include <sys/mman.h>
#include <sys/socket.h> // wayland
#include <sys/param.h> // MAXPATHLEN

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

#if __FRAMAC__
#include "system_header_spec.h"
#endif
