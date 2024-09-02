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
  const Mem_Region _prev_stack = STACK;

  const Path platform_dir = path_parent(path_realpath(path_from_cstr(__FILE__)));

  const Path assert_h = path_join(platform_dir, path_from_cstr("dev/assert.h"));
  const Path assert_c = path_join(platform_dir, path_from_cstr("dev/assert.c"));

  char gen_h[32 * 1024] = {0};
  char gen_c[32 * 1024] = {0};

  Fmt fh = fmt_new(gen_h, sizeof(gen_h));
  Fmt fc = fmt_new(gen_c, sizeof(gen_c));

  fmt_write(&fh, "%s", BANNER);
  fmt_write(&fc, "%s", BANNER);

  const char* const bin_condition_code[] = {"==", "!=", "<",   "<=",  ">",  ">="};
  const char* const bin_condition_name[] = {"eq", "ne", "lt", "lte", "gt", "gte"};

  const char* bin_condition_code_bin[ARRAY_LEN(bin_condition_code)];
  for(int i=0; i<ARRAY_LEN(bin_condition_code); ++i)
    bin_condition_code_bin[i] = str_fmt(&STACK, "x %s y", bin_condition_code[i]);

  const char* contract_begin = "//@ terminates true; assigns \\nothing; exits false;";

#define X(NAME, TYPE, FMT_CODE, CAST) { \
    fmt_write(&fh, "// ==== %s ====\n", #NAME); \
    for(int i=0; i<ARRAY_LEN(bin_condition_code); ++i) \
    { \
      fmt_write(&fh, "%s\n", contract_begin);\
      fmt_write(&fh, "void debug_assert_%s_%s(%s x, %s y);\n", #NAME, bin_condition_name[i], #TYPE, #TYPE); \
      fmt_write(&fh, "%s ensures %s;\n", contract_begin, bin_condition_code_bin[i]); \
      fmt_write(&fh, "void assert_%s_%s(%s x, %s y);\n", #NAME, bin_condition_name[i], #TYPE, #TYPE); \
    } \
    fmt_write(&fh, "\n"); \
  }
  X_MACRO_ASSERT_NUM_CMP_BIN(X)
#undef X

  file_text_create_from_cstr_if_different(assert_h, fh.begin);
  file_text_create_from_cstr_if_different(assert_c, fc.begin);

  // TODO: don't forget marking the condition as likely
  
  STACK = _prev_stack;
}

#undef X_MACRO_ASSERT_NUM_CMP_BIN
#undef X_MACRO_ASSERT_CUSTOM
#undef X_MACRO_ASSERT_NUM_CMP_RNG

