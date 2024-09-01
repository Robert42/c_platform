// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#define X_MACRO_ASSERT_NUM_CMP_BIN(X) \
  X(usize, usize, "%zu", /*no cast*/) \
  X(ssize, ssize, "%zs", /*no cast*/) \
  X(int, int, "%i", /*no cast*/) \
  X(ptr, const void*, "%p", /*cast*/(usize) ) \

#define X_MACRO_ASSERT_CUSTOM(X) \
  X(cstr_eq, const char*, (strcmp(x,y)==0), ) \
  X(bool_eq, bool, x==y, fmt_bool) \

#define X_MACRO_ASSERT_NUM_CMP_RNG(X) \
  X(usize, usize, "%zu", /*no cast*/) \
  X(ssize, ssize, "%zs", /*no cast*/) \
  X(ptr, const void*, "%p", /*cast*/(usize) ) \

static void platform_codegen_assertions();

void platform_codegen()
{
  platform_codegen_assertions();
}

static void platform_codegen_assertions()
{
  const Path platform_dir = path_parent(path_realpath(path_from_cstr(__FILE__)));

  const Path assert_h = path_join(platform_dir, path_from_cstr("dev/assert.h"));
  const Path assert_c = path_join(platform_dir, path_from_cstr("dev/assert.c"));

  char gen_h[32 * 1024] = {0};
  char gen_c[32 * 1024] = {0};

  char* gen_h_end = gen_h;
  char* gen_c_end = gen_c;

  gen_h_end += snprintf(gen_h_end, sizeof(gen_h)-(gen_h_end-gen_h), "%s", BANNER);
  assert_ptr_lt(gen_h_end, gen_h+sizeof(gen_h));
  
  gen_c_end += snprintf(gen_c_end, sizeof(gen_c)-(gen_c_end-gen_c), "%s", BANNER);
  assert_ptr_lt(gen_c_end, gen_c+sizeof(gen_c));

  file_text_create_from_cstr(assert_h, gen_h);
  file_text_create_from_cstr(assert_c, gen_c);
}

#undef X_MACRO_ASSERT_NUM_CMP_BIN
#undef X_MACRO_ASSERT_CUSTOM
#undef X_MACRO_ASSERT_NUM_CMP_RNG

