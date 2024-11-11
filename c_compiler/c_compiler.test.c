// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "c_compiler.h"

#define ASSERT_CC_CMF_EQ(CFG, EXPECTED) \
{ \
  struct C_Compiler_Config __cfg__ = (CFG); \
  char buf[4096] = {}; \
  Fmt f = fmt_new(buf, sizeof(buf)); \
  cc_command_fmt(&f, __cfg__); \
  assert_cstr_eq(f.begin, EXPECTED); \
}

void c_compiler_test()
{
  cc_init();

  // ==== different compilers & standards ====
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_GCC,
      .c_version = C_VERSION_1989,
      .skip_warning_flags = true,
      .c_file = path_from_cstr("x/y/z.c"),
      .output_file = path_from_cstr("hello_world"),
    }),
    "`gcc` `-std=c89` `-pedantic` `-o` `hello_world` `x/y/z.c`\n"
  );
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_TCC,
      .c_version = C_VERSION_1989,
      .skip_warning_flags = true,
      .c_file = path_from_cstr("main.c"),
      .output_file = path_from_cstr("hello_world"),
    }),
    "`tcc` `-o` `hello_world` `main.c`\n"
  );
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_CLANG,
      .c_version = C_VERSION_GNU_1999,
      .skip_warning_flags = true,
      .c_file = path_from_cstr("main.c"),
      .output_file = path_from_cstr("hello_world"),
    }),
    "`clang` `-std=gnu99` `-o` `hello_world` `main.c`\n"
  );

  // ==== warnings & errors ====
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_GCC,
      .disable_vla = true,
      .skip_warning_flags = true,
      .c_version = C_VERSION_1999,
      .c_file = path_from_cstr("main.c"),
    }),
    "`gcc` `-std=c99` `-pedantic` `-Werror=vla` `main.c`\n"
  );
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_GCC,
      .disable_vla = true,
      .c_version = C_VERSION_1999,
      .c_file = path_from_cstr("main.c"),
    }),
    "`gcc` `-std=c99` `-pedantic` "
    "`-Wall` "
    "`-Wextra` "
    "`-Werror` "
    "`-Wno-error=unused-parameter` "
    "`-Wno-error=unused-variable` "
    "`-Wno-error=unused-function` "
    "`-Wno-error=unused-but-set-variable` "
    "`-Wno-error=sign-compare` "
    "`-Wno-error=uninitialized` "
    "`-Wno-error=pedantic` "
    "`-Werror=vla` "
    "`main.c`\n"
  );
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_TCC,
      .disable_vla = true,
      .c_version = C_VERSION_1999,
      .c_file = path_from_cstr("main.c"),
      .skip_warning_flags = false,
      .debug = false,
      .capture_run_stdout = false,
    }),
    "`tcc` "
    "`-Wall` "
    // "`-Wunsupported` "
    "`-Werror` "
    "`main.c`\n"
  );

  // ==== debug ====
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_TCC,
      .debug = true,
      .skip_warning_flags = true,
      .c_version = C_VERSION_1999,
      .c_file = path_from_cstr("main.c"),
    }),
    "`tcc` `-g` `main.c`\n"
  );

  // ==== debug ====
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_GCC,
      .debug = true,
      .sanitize_memory = true,
      .skip_warning_flags = true,
      .c_version = C_VERSION_1999,
      .c_file = path_from_cstr("main.c"),
    }),
    "`gcc` `-g` `-fsanitize=address` `-fsanitize=pointer-compare` `-fsanitize=pointer-subtract` `-fsanitize=undefined` `-fsanitize-address-use-after-scope` `-fstack-protector-all` `-std=c99` `-pedantic` `main.c`\n"
  );
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_TCC,
      .debug = true,
      .sanitize_memory = true,
      .skip_warning_flags = true,
      .c_version = C_VERSION_1999,
      .c_file = path_from_cstr("main.c"),
    }),
    "`tcc` `-g` `main.c`\n"
  );

  // ==== run ====
  const char* args[] = {"x y z", "uvw", "abc"};
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_TCC,
      .debug = true,
      .skip_warning_flags = true,
      .c_version = C_VERSION_1999,
      .c_file = path_from_cstr("main.c"),
      .run_args = args,
      .run_args_count = 0,
      .output_file = path_from_cstr("bin/exe"), // no outut file when running with tcc
    }),
    "`tcc` `-g` `-run` `main.c`\n"
  );
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_GCC,
      .debug = true,
      .skip_warning_flags = true,
      .c_version = C_VERSION_GNU_2011,
      .c_file = path_from_cstr("main.c"),
      .run_args = args,
      .run_args_count = 0,
      .output_file = path_from_cstr("bin/exe"),
    }),
    "`gcc` `-g` `-std=gnu11` `-o` `bin/exe` `main.c`\n"
    "`bin/exe`\n"
  );
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_TCC,
      .debug = true,
      .skip_warning_flags = true,
      .c_version = C_VERSION_1999,
      .c_file = path_from_cstr("main.c"),
      .run_args = args,
      .run_args_count = 2,
      .output_file = path_from_cstr("bin/exe"), // no outut file when running with tcc
    }),
    "`tcc` `-g` `-run` `main.c` `x y z` `uvw`\n"
  );
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_GCC,
      .debug = true,
      .skip_warning_flags = true,
      .c_version = C_VERSION_GNU_2011,
      .c_file = path_from_cstr("main.c"),
      .run_args = args,
      .run_args_count = 2,
      .output_file = path_from_cstr("bin/exe"),
    }),
    "`gcc` `-g` `-std=gnu11` `-o` `bin/exe` `main.c`\n"
    "`bin/exe` `x y z` `uvw`\n"
  );

  // ==== capture ====
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_GCC,
      .debug = true,
      .skip_warning_flags = true,
      .c_version = C_VERSION_GNU_1989,
      .c_file = path_from_cstr("main.c"),
      .run_args = args,
      .run_args_count = 0,
      .output_file = path_from_cstr("bin/exe"),
      .capture_run_stdout = true,
      .capture_run_stdout_filepath = path_from_cstr("abc.txt"),
    }),
    "`gcc` `-g` `-std=gnu89` `-o` `bin/exe` `main.c`\n"
    "`bin/exe` `>` `abc.txt`\n"
  );

  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_GCC,
      .debug = true,
      .skip_warning_flags = true,
      .c_version = C_VERSION_GNU_1989,
      .c_file = path_from_cstr("main.c"),
      .run_args = args,
      .run_args_count = 0,
      .output_file = path_from_cstr("bin/exe"),
      .capture_run_stderr = true,
      .capture_run_stderr_filepath = path_from_cstr("abc.txt"),
    }),
    "`gcc` `-g` `-std=gnu89` `-o` `bin/exe` `main.c`\n"
    "`bin/exe` `2>` `abc.txt`\n"
  );

  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_GCC,
      .debug = true,
      .skip_warning_flags = true,
      .c_version = C_VERSION_GNU_1989,
      .c_file = path_from_cstr("main.c"),
      .run_args = args,
      .run_args_count = 0,
      .output_file = path_from_cstr("bin/exe"),
      .capture_run_stdout = true,
    }),
    "`gcc` `-g` `-std=gnu89` `-o` `bin/exe` `main.c`\n"
    "`bin/exe` `>` `/dev/null`\n"
  );

  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_GCC,
      .debug = true,
      .skip_warning_flags = true,
      .c_version = C_VERSION_GNU_1989,
      .c_file = path_from_cstr("main.c"),
      .run_args = args,
      .run_args_count = 0,
      .output_file = path_from_cstr("bin/exe"),
      .capture_run_stderr = true,
    }),
    "`gcc` `-g` `-std=gnu89` `-o` `bin/exe` `main.c`\n"
    "`bin/exe` `2>` `/dev/null`\n"
  );

  // ==== include dir ====
  Path include_a_b_c = path_from_cstr("a/b/c");
  Path include_x_y_z = path_from_cstr("x/y/z");

  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_GCC,
      .debug = false,
      .include_dir = {&include_a_b_c, &include_x_y_z},
      .include_dir_count = 2,
      .skip_warning_flags = true,
      .c_version = C_VERSION_GNU_1989,
      .c_file = path_from_cstr("main.c"),
    }),
    "`gcc` `-std=gnu89` `-Ia/b/c` `-Ix/y/z` `main.c`\n"
  );

  // ==== static analysis ====
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_GCC,
      .debug = false,
      .skip_warning_flags = true,
      .c_version = C_VERSION_GNU_1989,
      .c_file = path_from_cstr("main.c"),
      .static_analysis = true,
    }),
    "`gcc` `-fanalyzer` `-Wanalyzer-too-complex` `-std=gnu89` `main.c`\n"
  );
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_CLANG,
      .debug = false,
      .skip_warning_flags = true,
      .c_version = C_VERSION_1999,
      .c_file = path_from_cstr("main.c"),
      .static_analysis = true,
    }),
    "`clang` `--analyze` `-Xclang` `-analyzer-config` `-Xclang` `crosscheck-with-z3=true` `-std=c99` `-pedantic` `main.c`\n"
  );
}

#undef ASSERT_CC_CMF_EQ

