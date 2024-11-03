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
      .skip_waning_flags = true,
      .c_file = path_from_cstr("x/y/z.c"),
      .output_file = path_from_cstr("hello_world"),
    }),
    "`gcc` `-std=c89` `-pedantic` `x/y/z.c` `-o` `hello_world`\n"
  );
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_TCC,
      .c_version = C_VERSION_1989,
      .skip_waning_flags = true,
      .c_file = path_from_cstr("main.c"),
      .output_file = path_from_cstr("hello_world"),
    }),
    "`tcc` `main.c` `-o` `hello_world`\n"
  );
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_CLANG,
      .c_version = C_VERSION_GNU_1999,
      .skip_waning_flags = true,
      .c_file = path_from_cstr("main.c"),
      .output_file = path_from_cstr("hello_world"),
    }),
    "`clang` `-std=gnu99` `main.c` `-o` `hello_world`\n"
  );

  // ==== warnings & errors ====
  ASSERT_CC_CMF_EQ(
    ((struct C_Compiler_Config){
      .cc = CC_GCC,
      .disable_vla = true,
      .skip_waning_flags = true,
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
    }),
    "`tcc` "
    "`-Wall` "
    "`-Wunsupported` "
    "`-Werror` "
    "`main.c`\n"
  );
}

#undef ASSERT_CC_CMF_EQ

