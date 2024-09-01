// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

static void platform_codegen_assertions();

void platform_codegen()
{
  platform_codegen_assertions();
}

struct _Platform_Codegen_Assert_Fn
{
  const char* arg_ty[3];
  const char* arg_name[3];
  const char* condition;
  const char* cast;
};

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

  create_text_file_cstr(assert_h, gen_h);
  create_text_file_cstr(assert_c, gen_c);
}
