// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#ifdef NDEBUG
#define ENV_DEBUG 0
#else
#define ENV_DEBUG 1
#endif

#define COMPILER_TCC 1

#if defined(__TINYC__)
#define ENV_COMPILER COMPILER_TCC
#else
#error unknown compiler
#endif

void dev_env_demo();
