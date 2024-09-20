// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "gen_table.h"

const char* test_autogen_table_fmt(Mem_Region* region, struct Autogen_Table table)
{
  Fmt f_h_decl = fmt_new_from_region(region, 15*MiB);
  Fmt f_h = fmt_new_from_region(region, 5*MiB);
  Fmt f_c = fmt_new_from_region(region, 5*MiB);

  _autogen_table_fmt(&f_h_decl, &f_h, &f_c, table);

  fmt_write(&f_h_decl, "\n/*<< *.h >>*/\n%s", f_h.begin);
  fmt_write(&f_h_decl, "\n/*<< *.c >>*/\n%s", f_c.begin);

  return f_h_decl.begin;
}

void gen_table_test()
{
  const Mem_Region _prev_stack = STACK;

  struct Autogen_Table table = {
    .name = "Entity",
  };

  assert_cstr_eq(test_autogen_table_fmt(&STACK, table),
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
