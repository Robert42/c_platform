// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "gen_adt.h"

const char* test_autogen_adt_fmt(Mem_Region* region, struct Autogen_ADT adt)
{
  Fmt f_h_decl = fmt_new_from_region(region, 15*MiB);
  Fmt f_h = fmt_new_from_region(region, 5*MiB);
  Fmt f_c = fmt_new_from_region(region, 5*MiB);

  _autogen_adt_fmt(&f_h_decl, &f_h, &f_c, adt);

  fmt_write(&f_h_decl, "\n/*<< *.h >>*/\n%s", f_h.begin);
  fmt_write(&f_h_decl, "\n/*<< *.c >>*/\n%s", f_c.begin);

  return f_h_decl.begin;
}

void gen_adt_test()
{
  const Mem_Region _prev_stack = STACK;

  struct Autogen_ADT adt = {
    .name = "Entity",
  };

  assert_cstr_eq(test_autogen_adt_fmt(&STACK, adt),
    "// ${BANNER}\n"
    "enum Entity_Variant;\n"
    "struct Entity_ID;\n"
    "struct Entity;\n"
    "\n"
    "/*<< *.h >>*/\n"
    "// ${BANNER}\n"
    "\n"
    "/*<< *.c >>*/\n"
    "// ${BANNER}\n"
  );
  STACK = _prev_stack;
}
