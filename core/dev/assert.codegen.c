// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#define X_MACRO_ASSERT_NUM_CMP_BIN(X) \
  X(usize, usize, "%zu", /*no cast*/, NULL) \
  X(ssize, ssize, "%zd", /*no cast*/, NULL) \
  X(int, int, "%i", /*no cast*/, NULL) \
  X(char, char, "'%c'", /*no cast*/, NULL) \
  X(ptr, const void*, "%p", /*cast*/(usize) , NULL) \

// ISSUE_FRAMA_C: add to contract of cstr_eq: ensure, that both strings are equal
#define X_MACRO_ASSERT_CUSTOM(X) \
  X(cstr_eq, " == ", "", const char*, (strcmp(x,y) == 0), /*no fmt*/ , "print_cstr_diff(x, y)") \
  X(str_eq, " == ", "", str, (str_cmp(x,y) == 0), str_fmt, "print_str_diff(x, y)") \
  X(bool_eq, " == ", " admit ensures x == y;", bool, x == y, fmt_bool, NULL) \

#define X_MACRO_ASSERT_NUM_CMP_RNG(X) \
  X(usize) \
  X(ssize) \
  X(ptr) \

struct Codegen_Assert
{
  const char* name; // "assert_usize_lte_lt"
  const char* type; // "usize"
  const char* condition; // "x <= y && y < z"
  const char* contract; // "x <= y < z"
  const char* panic; // "__ter_assert_failed__(condition, cstr_fmt(&PANIC_REGION, \"%zu\", x), cstr_fmt(&PANIC_REGION, \"%zu\", y), cstr_fmt(&PANIC_REGION, \"%zu\", z), file, line);"
  const char* pretty_print_comparison[5]; // {"", " <= ", " < ", ""}
  const char* diff;
  unsigned int num_args : 2; // 3 in case of `assert_usize_lte_lt`
};

struct Codegen_Assert_Group
{
  const char* name; // "ptr"
  unsigned int begin, end; // range of slice of Codegen_Assert withign this group
};

static void codegen_assertion_define(Fmt* f, const char** arg_name, struct Codegen_Assert a, const char* prefix, bool call_proc);
static void assert_codegen()
{
  const Mem_Region _prev_stack = STACK;

  const Path core_dir = path_parent(path_parent(path_realpath(path_from_cstr(__FILE__))));

  const Path assert_h = path_join(core_dir, path_from_cstr("dev/assert.generated.h"));
  const Path assert_c = path_join(core_dir, path_from_cstr("dev/assert.generated.c"));

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

#undef CMP_EQ
#undef CMP_NE
#undef CMP_LT
#undef CMP_LTE
#undef CMP_GT
#undef CMP_GTE

  struct Codegen_Assert assertions[1024];
  struct Codegen_Assert_Group assert_group[256];
  int num_assertions = 0;
  int num_assert_groups = 0;

#define OR_STRCMP(X) || strcmp(#X, name)==0
#define CREATE_RANGE(X) (false X(OR_STRCMP))

#define X(NAME, TYPE, FMT_CODE, CAST, DIFF) { \
    const char* const name = #NAME; \
    const int first_assert = num_assertions; \
    for(usize xy=0; xy<ARRAY_LEN(bin_condition_code); ++xy) \
    { \
      const char* condition = cstr_fmt(&STACK, "x %s y", bin_condition_code[xy]); \
      assertions[num_assertions++] = (struct Codegen_Assert){ \
        .name = cstr_fmt(&STACK, "assert_%s_%s", #NAME, bin_condition_name[xy]), \
        .type = #TYPE, \
        .condition = condition, \
        .contract = cstr_fmt(&STACK, " admit ensures %s;", condition), \
        .panic = cstr_fmt(&STACK, "__bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, %s, x), cstr_fmt(&PANIC_REGION, %s, y), file, line);\n", #FMT_CODE, #FMT_CODE), \
        .pretty_print_comparison = {NULL, cstr_fmt(&STACK, " %s ", bin_condition_code[xy]), NULL}, \
        .num_args = 2, \
      }; \
    } \
    if(CREATE_RANGE(X_MACRO_ASSERT_NUM_CMP_RNG)) \
    { \
      for(usize i=0; i<ARRAY_LEN(rng_conditions); ++i) \
      { \
        const u16 xy = rng_conditions[i]>>8; \
        const u16 yz = rng_conditions[i] & 0xff; \
        assertions[num_assertions++] = (struct Codegen_Assert){ \
          .name = cstr_fmt(&STACK, "assert_%s_%s_%s", #NAME, bin_condition_name[xy], bin_condition_name[yz]), \
          .type = #TYPE, \
          .condition = cstr_fmt(&STACK, "x %s y && y %s z", bin_condition_code[xy], bin_condition_code[yz]), \
          .contract = cstr_fmt(&STACK, " admit ensures x %s y %s z;", bin_condition_code[xy], bin_condition_code[yz]), \
          .panic = cstr_fmt(&STACK, "__ter_assert_failed__(condition, cstr_fmt(&PANIC_REGION, %s, x), cstr_fmt(&PANIC_REGION, %s, y), cstr_fmt(&PANIC_REGION, %s, z), file, line);\n", #FMT_CODE, #FMT_CODE, #FMT_CODE), \
          .pretty_print_comparison = {NULL, cstr_fmt(&STACK, " %s ", bin_condition_code[xy]), cstr_fmt(&STACK, " %s ", bin_condition_code[yz]), NULL}, \
          .diff = (DIFF), \
          .num_args = 3, \
        }; \
      } \
    } \
    assert_group[num_assert_groups++] = (struct Codegen_Assert_Group){ \
      .name = #NAME, \
      .begin = first_assert, \
      .end = num_assertions, \
    }; \
  }
  X_MACRO_ASSERT_NUM_CMP_BIN(X)
#undef X

#define X(NAME, PRINT_MID, ENSURES, TYPE, CONDITION, FMT_CODE, DIFF) { \
    const int first_assert = num_assertions; \
    assertions[num_assertions++] = (struct Codegen_Assert){ \
      .name = cstr_fmt(&STACK, "assert_%s", #NAME), \
      .type = #TYPE, \
      .condition = #CONDITION, \
      .contract = ENSURES, \
      .panic = cstr_fmt(&STACK, "__bin_assert_failed__(condition, %s(x), %s(y), file, line);\n", #FMT_CODE, #FMT_CODE), \
      .pretty_print_comparison = {NULL, PRINT_MID, NULL}, \
      .diff = (DIFF), \
      .num_args = 2, \
    }; \
    assert_group[num_assert_groups++] = (struct Codegen_Assert_Group){ \
      .name = #NAME, \
      .begin = first_assert, \
      .end = num_assertions, \
    }; \
  }
  X_MACRO_ASSERT_CUSTOM(X)
#undef X

#undef OR_STRCMP
#undef CREATE_RANGE

  const bool dbg = false;

  // ==== assert procedures ====
  fmt_write(&fc, "#ifndef __FRAMAC__\n\n");
  const char* arg_name[] = {"x", "y", "z"};
  for(int group_idx=0; group_idx<num_assert_groups; ++group_idx)
  {
    struct Codegen_Assert_Group g = assert_group[group_idx];

    if(dbg)
      printf("// ==== %s ====\n", g.name);
    fmt_write(&fh, "// ==== %s ====\n", g.name);
    fmt_write(&fc, "// ==== %s ====\n", g.name);
    
    for(usize assert_idx=g.begin; assert_idx<g.end; ++assert_idx)
    {
      struct Codegen_Assert a = assertions[assert_idx];
      assert_usize_lte(a.num_args, ARRAY_LEN(arg_name)); // Need more names

      if(assert_idx>g.begin && assertions[assert_idx-1].num_args != a.num_args)
        fmt_write(&fh, "\n");

      if(dbg)
      {
        printf("Codegen_Assert{\n");
        printf("  .name = `%s`\n", a.name);
        printf("  .type = `%s`\n", a.type);
        printf("  .condition = `%s`\n", a.condition);
        printf("  .contract = `%s`\n", a.contract);
        printf("  .panic = `%s`\n", a.panic);
        if(a.diff)
          printf("  .diff = `%s`\n", a.diff);
        else
          printf("  .diff = NULL\n");
        printf("  .pretty_print_comparison = {");
        for(int arg_idx=0; arg_idx<=a.num_args; ++arg_idx)
          if(a.pretty_print_comparison[arg_idx])
            printf("\"%s\",", a.pretty_print_comparison[arg_idx]);
          else
            printf("NULL,");
        printf("},\n");
        printf("  .num_args = `%u`\n", a.num_args);
        printf("}\n");
      }
      fmt_write(&fh, "//@ terminates true; assigns \\nothing; exits false;%s\n", a.contract);
      const char* signature_begin = fh.end;
      fmt_write(&fh, "void __%s__(", a.name);
      for(int arg_idx=0; arg_idx<a.num_args; ++arg_idx)
        fmt_write(&fh, "%s%s %s", arg_idx?", ":"", a.type, arg_name[arg_idx]);
      fmt_write(&fh, ", const char* condition, const char* file, int line)");
      fmt_write(&fc, "%s", signature_begin); // Here, the segnature is anultlermianted string
      fmt_write(&fh, ";\n");

      fmt_write(&fc, "\n{\n");
      fmt_write(&fc, "  if(LIKELY(%s))\n", a.condition);
      fmt_write(&fc, "    return;\n");
      fmt_write(&fc, "  else\n");
      if(a.diff != NULL)
      {
        fmt_write(&fc, "  {\n");
        fmt_write(&fc, "    if(ASSERT_SHOW_DIFF && !__assert_capture__)\n");
        fmt_write(&fc, "      %s;\n", a.diff);
      }
      fmt_write(&fc, "  %s", a.panic);
      if(a.diff != NULL)
        fmt_write(&fc, "  }\n");
      fmt_write(&fc, "}\n");

      
    }
    fmt_write(&fh, "\n");
    fmt_write(&fc, "\n");
  }

  fmt_write(&fc, "#endif // __FRAMAC__\n");
  // ==== assert macros ====
  for(int group_idx=0; group_idx<num_assert_groups; ++group_idx)
  {
    struct Codegen_Assert_Group g = assert_group[group_idx];

    fmt_write(&fh, "// ==== %s ====\n", g.name);

    for(usize assert_idx=g.begin; assert_idx<g.end; ++assert_idx)
    {
      struct Codegen_Assert a = assertions[assert_idx];
      assert_usize_lte(a.num_args, ARRAY_LEN(arg_name)); // Need more names

      if(assert_idx>g.begin && assertions[assert_idx-1].num_args != a.num_args)
        fmt_write(&fh, "\n");

      codegen_assertion_define(&fh, arg_name, a, "", true);
    }
    fmt_write(&fh, "\n");
  }

  // ==== debug assert macros ====
  fmt_write(&fh, "#if defined(__FRAMAC__) || !ENV_DEBUG\n");
  for(int group_idx=0; group_idx<num_assert_groups; ++group_idx)
  {
    struct Codegen_Assert_Group g = assert_group[group_idx];

    fmt_write(&fh, "// ==== %s ====\n", g.name);

    for(usize assert_idx=g.begin; assert_idx<g.end; ++assert_idx)
    {
      struct Codegen_Assert a = assertions[assert_idx];
      assert_usize_lte(a.num_args, ARRAY_LEN(arg_name)); // Need more names

      if(assert_idx>g.begin && assertions[assert_idx-1].num_args != a.num_args)
        fmt_write(&fh, "\n");

      codegen_assertion_define(&fh, arg_name, a, "debug_", false);
    }
    fmt_write(&fh, "\n");
  }
  fmt_write(&fh, "#else // __FRAMAC__ || !ENV_DEBUG\n");
  for(int group_idx=0; group_idx<num_assert_groups; ++group_idx)
  {
    struct Codegen_Assert_Group g = assert_group[group_idx];

    fmt_write(&fh, "// ==== %s ====\n", g.name);
    
    for(usize assert_idx=g.begin; assert_idx<g.end; ++assert_idx)
    {
      struct Codegen_Assert a = assertions[assert_idx];
      assert_usize_lte(a.num_args, ARRAY_LEN(arg_name)); // Need more names

      if(assert_idx>g.begin && assertions[assert_idx-1].num_args != a.num_args)
        fmt_write(&fh, "\n");

      codegen_assertion_define(&fh, arg_name, a, "debug_", true);
    }
    fmt_write(&fh, "\n");
  }
  fmt_write(&fh, "#endif // __FRAMAC__ || !ENV_DEBUG\n");
  
  file_text_create_from_cstr_if_different(assert_h, fh.begin);
  file_text_create_from_cstr_if_different(assert_c, fc.begin);

  STACK = _prev_stack;

#undef OR_STRCMP
#undef CREATE_RANGE
}

static void codegen_assertion_define(Fmt* f, const char** arg_name, struct Codegen_Assert a, const char* prefix, bool call_proc)
{
  fmt_write(f, "#define %s%s(", prefix, a.name);
  for(int arg_idx=0; arg_idx<a.num_args; ++arg_idx)
    fmt_write(f, "%s%s", arg_idx?", ":"", arg_name[arg_idx]);
  fmt_write(f, ")");

  if(call_proc)
  {
    fmt_write(f, " __%s__(", a.name);
    for(int arg_idx=0; arg_idx<a.num_args; ++arg_idx)
      fmt_write(f, "%s%s", arg_idx?", ":"", arg_name[arg_idx]);
    fmt_write(f, ",");
    for(int arg_idx=0; arg_idx<=a.num_args; ++arg_idx)
    {
      const char* snippet = a.pretty_print_comparison[arg_idx];
      if(snippet)
        fmt_write(f, " \"%s\"", snippet);
      if(arg_idx < a.num_args)
        fmt_write(f, " #%s", arg_name[arg_idx]);
    }
    fmt_write(f, ", __FILE__, __LINE__)");
  }
  fmt_write(f, "\n");
}

#undef X_MACRO_ASSERT_NUM_CMP_BIN
#undef X_MACRO_ASSERT_CUSTOM
#undef X_MACRO_ASSERT_NUM_CMP_RNG

