// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

size_t _assert_capture = 0;
size_t _assert_captured = 0;

static void __assert_failed__()
{
  if(_assert_capture)
  {
    _assert_captured++;
    return;
  }

  printf("%s==== ASSERT ====%s\n", TERM_RED, TERM_NORMAL);
  abort();
}

void assert_usize_eq(size_t x, size_t y)
{
  if(x == y)
    return;
  __assert_failed__();
}

void assert_usize_lt(size_t x, size_t y)
{
  if(x < y)
    return;
  __assert_failed__();
}

void assert_ptr_eq(const void* x, const void* y)
{
  if(x == y)
    return;
  __assert_failed__();
}

void debug_assert_usize_lt(size_t x, size_t y)
{
#if ENV_DEBUG
  if(x < y)
    return;
  __assert_failed__();
#endif
}

void debug_assert_ptr_lte(const void* x, const void* y)
{
#if ENV_DEBUG
  if(x <= y)
    return;
  __assert_failed__();
#endif
}

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


#ifdef __linux__
void __linux_call_failed__(const char* call, const char* file, int line)
{
  if(_assert_capture)
  {
    _assert_captured++;
    return;
  }

  printf("%s==== ASSERT_LINUX ====%s\n", TERM_RED, TERM_RED_BOLD);
  perror(call);
  printf("%s%s:%d\n", TERM_NORMAL, __FILE__, __LINE__);
  abort();
}
#endif
