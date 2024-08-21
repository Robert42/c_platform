// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

size_t _assert_capture = 0;
size_t _assert_captured = 0;

#define CAPTURE if(_assert_capture) {_assert_captured++; return;}

void assert_usize_eq(size_t x, size_t y)
{
  if(x != y)
    abort();
}

void assert_ptr_eq(const void* x, const void* y)
{
  if(x != y)
    abort();
}

void debug_assert_usize_lt(const void* x, const void* y)
{
#if ENV_DEBUG
  if(x < y)
    return;
  CAPTURE
  abort();
#endif
}

#undef CAPTURE

// ==== env ====

static inline const char* dev_env_compiler_name(int compiler_id)
{
#define CASE(X) case X: return #X;
  switch(compiler_id)
  {
  CASE(COMPILER_TCC)
  CASE(COMPILER_GCC)
  }
  abort();
#undef CASE
}

void dev_env_demo()
{
  printf("ENV_DEBUG: %i\n", ENV_DEBUG);
  printf("ENV_COMPILER: %s\n", dev_env_compiler_name(ENV_COMPILER));
}


