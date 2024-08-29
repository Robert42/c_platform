// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#ifdef NDEBUG
#define ENV_DEBUG 0
#else
#define ENV_DEBUG 1
#endif

#define COMPILER_TCC 1
#define COMPILER_GCC 2
#define COMPILER_CLANG 3

#define ARCH_AARCH64 1
#define ARCH_X86_16 2
#define ARCH_X86_32 3
#define ARCH_X86_64 4

#if defined(__TINYC__)
#define ENV_COMPILER COMPILER_TCC
#elif defined(__clang__)
#define ENV_COMPILER COMPILER_CLANG
#elif defined(__GNUC__)
#define ENV_COMPILER COMPILER_GCC
#else
#error unknown compiler
#endif

#if defined(__aarch64__)
#define ENV_ARCH ARCH_AARCH64
#else
#error unsupported
#endif

void dev_env_demo();
