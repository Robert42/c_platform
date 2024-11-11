// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#ifdef NDEBUG
#define ENV_DEBUG 0
#else
#define ENV_DEBUG 1
#endif

#if defined(__FRAMAC__)
#define ENV_STATIC_ANALYSIS 1
#define GHOST 1
#else
#define ENV_STATIC_ANALYSIS 0
#define GHOST 0
#endif

#define COMPILER_TCC 1
#define COMPILER_GCC 2
#define COMPILER_CLANG 3
#define COMPILER_FRAMAC 4

#define ARCH_AARCH64 1
#define ARCH_X86_16 2
#define ARCH_X86_32 3
#define ARCH_X86_64 4

#if defined(__TINYC__)
#define ENV_COMPILER COMPILER_TCC
#elif defined(__FRAMAC__)
#define ENV_COMPILER COMPILER_FRAMAC
#elif defined(__clang__)
#define ENV_COMPILER COMPILER_CLANG
#elif defined(__GNUC__)
#define ENV_COMPILER COMPILER_GCC
#else
#error unknown compiler
#endif

#if defined(__aarch64__)
#define ENV_ARCH ARCH_AARCH64
#elif defined(__x86_64__)
#define ENV_ARCH ARCH_AARCH64
#else
#error unsupported
#endif

#if ENV_ARCH==ARCH_AARCH64 || \
  ENV_ARCH==ARCH_X86_64
#define ENV_PTR_BITS 64
#elif ENV_ARCH==ARCH_X86_32
#define ENV_PTR_BITS 32
#elif ENV_ARCH==ARCH_X86_16
#define ENV_PTR_BITS 16
#else
#error unsupported
#endif

void dev_env_demo();

#define alignof __alignof__
