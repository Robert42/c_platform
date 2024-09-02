// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#define X_MACRO_ASSERT_NUM_CMP_BIN(X) \
  X(usize, usize, "%zu", /*no cast*/) \
  X(ssize, ssize, "%zs", /*no cast*/) \
  X(int, int, "%i", /*no cast*/) \
  X(ptr, const void*, "%p", /*cast*/(usize) ) \

// TODO: ensure, that both strings are equal
#define X_MACRO_ASSERT_CUSTOM(X) \
  X(cstr_eq, "", const char*, (strcmp(x,y)==0), ) \
  X(bool_eq, " ensures x == y;", bool, x==y, fmt_bool) \

#define X_MACRO_ASSERT_NUM_CMP_RNG(X) \
  X(usize) \
  X(ssize) \
  X(ptr) \

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

#define CMP_EQ 0
#define CMP_NE 1
#define CMP_LT 2
#define CMP_LTE 3
#define CMP_GT 4
#define CMP_GTE 5

  const char* const bin_condition_code[] = {
    [CMP_EQ] = "==",
    [CMP_NE] = "!=",
    [CMP_LT] = "<",
    [CMP_LTE] = "<=",
    [CMP_GT] = ">",
    [CMP_GTE] = ">=",
   };
  const char* const bin_condition_name[] = {
    [CMP_EQ] = "eq",
    [CMP_NE] = "ne",
    [CMP_LT] = "lt",
    [CMP_LTE] = "lte",
    [CMP_GT] = "gt",
    [CMP_GTE] = "gte",
  };
  const u16 rng_conditions[] = {
    (CMP_LTE << 8) | CMP_LTE,
    (CMP_LTE << 8) | CMP_LT,
  };

  const char* bin_condition_code_bin[ARRAY_LEN(bin_condition_code)];
  for(int i=0; i<ARRAY_LEN(bin_condition_code); ++i)
    bin_condition_code_bin[i] = str_fmt(&STACK, "x %s y", bin_condition_code[i]);

  const char* contract_begin = "//@ terminates true; assigns \\nothing; exits false;";

#undef CMP_EQ
#undef CMP_NE
#undef CMP_LT
#undef CMP_LTE
#undef CMP_GT
#undef CMP_GTE

#define OR_STRCMP(X) || strcmp(#X, name)==0
#define CREATE_RANGE(X) (false X(OR_STRCMP))

#define X(NAME, TYPE, FMT_CODE, CAST) { \
    const char* const name = #NAME; \
    fmt_write(&fh, "// ==== %s ====\n", name); \
    for(int i=0; i<ARRAY_LEN(bin_condition_code); ++i) \
    { \
      fmt_write(&fh, "%s\n", contract_begin);\
      fmt_write(&fh, "void debug_assert_%s_%s(%s x, %s y);\n", name, bin_condition_name[i], #TYPE, #TYPE); \
      fmt_write(&fh, "%s ensures %s;\n", contract_begin, bin_condition_code_bin[i]); \
      fmt_write(&fh, "void assert_%s_%s(%s x, %s y);\n", name, bin_condition_name[i], #TYPE, #TYPE); \
    } \
    if(CREATE_RANGE(X_MACRO_ASSERT_NUM_CMP_RNG)) \
    { \
      fmt_write(&fh, "\n"); \
      for(int i=0; i<ARRAY_LEN(rng_conditions); ++i) \
      { \
        const u16 xy = rng_conditions[i]>>8; \
        const u16 yz = rng_conditions[i] & 0xff; \
        fmt_write(&fh, "void debug_assert_%s_%s_%s(%s x, %s y, %s z);\n", name, bin_condition_name[xy], bin_condition_name[yz], #TYPE, #TYPE, #TYPE); \
        fmt_write(&fh, "%s ensures x %s y %s z;\n", contract_begin, bin_condition_code[xy], bin_condition_code[yz]); \
        fmt_write(&fh, "void assert_%s_%s_%s(%s x, %s y, %s z);\n", name, bin_condition_name[xy], bin_condition_name[yz], #TYPE, #TYPE, #TYPE); \
      } \
    } \
    fmt_write(&fh, "\n"); \
  }
  X_MACRO_ASSERT_NUM_CMP_BIN(X)
#undef X

#define X(NAME, ENSURES, TYPE, FMT_CODE, CAST) { \
    fmt_write(&fh, "// ==== %s ====\n", #NAME); \
    fmt_write(&fh, "%s\n", contract_begin);\
    fmt_write(&fh, "void debug_assert_%s(%s x, %s y);\n", #NAME, #TYPE, #TYPE); \
    fmt_write(&fh, "%s%s\n", contract_begin, ENSURES);\
    fmt_write(&fh, "void assert_%s(%s x, %s y);\n", #NAME, #TYPE, #TYPE); \
    fmt_write(&fh, "\n"); \
  }
  X_MACRO_ASSERT_CUSTOM(X)
#undef X

  file_text_create_from_cstr_if_different(assert_h, fh.begin);
  file_text_create_from_cstr_if_different(assert_c, fc.begin);

  // TODO: don't forget marking the condition as likely
  
  STACK = _prev_stack;
}

#undef X_MACRO_ASSERT_NUM_CMP_BIN
#undef X_MACRO_ASSERT_CUSTOM
#undef X_MACRO_ASSERT_NUM_CMP_RNG

