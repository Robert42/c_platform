// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#define NORETURN __attribute__((noreturn))
#define UNUSED __attribute__((unused))

// TODO use intrinsic
#define LIKELY(X) X
