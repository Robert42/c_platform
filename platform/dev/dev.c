// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

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
