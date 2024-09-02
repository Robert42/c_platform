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

  Fmt fh = fmt_new(gen_h, sizeof(gen_h));
  Fmt fc = fmt_new(gen_c, sizeof(gen_c));

  fmt(&fh, "%s", BANNER);

  fmt(&fc, "%s", BANNER);

  file_text_create_from_cstr(assert_h, fh.begin);
  file_text_create_from_cstr(assert_c, fc.begin);

  // TODO: don't forget marking the condition as likely
}

#undef X_MACRO_ASSERT_NUM_CMP_BIN
#undef X_MACRO_ASSERT_CUSTOM
#undef X_MACRO_ASSERT_NUM_CMP_RNG

