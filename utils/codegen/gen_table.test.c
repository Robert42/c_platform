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

  

#if 0
  struct Autogen_Table_Column expr_bin_table_columns[] = {
    { .type = "enum Op_Bin", .name = "op", },
    { .type = "Expr_ID", .name = "x", },
    { .type = "Expr_ID", .name = "y", },
  };

  struct Autogen_Table distinct_tables[] = {
    {
      .name = "Bin",
      .columns = expr_bin_table_columns,
      .num_columns = ARRAY_LEN(expr_bin_table_columns),
    },
  };
#endif
  struct Autogen_Table table = {
    .nodes = NULL,
    .columns = NULL,
#if 0

    .distinct_tables = distinct_tables,
    .num_distinct = ARRAY_LEN(distinct_tables),
#endif
  };

  assert_cstr_eq(test_autogen_table_fmt(&STACK, table),
    "// ${BANNER}\n"
#if 0
    "enum Expr_Variant;\n"
    "typedef struct _struct_Expr_ID Expr_ID;\n"
    "struct Expr_Table;\n"
    "struct Expr;\n"
    "struct Expr_Bin;\n"
#endif
    "\n"
    "/*<< *.h >>*/\n"
    "// ${BANNER}\n"
#if 0
    "enum Expr_Variant\n"
    "{\n"
    "  EXPR_BIN,\n"
    "};\n"
    "\n"
    "struct _struct_Expr_ID\n"
    "{\n"
    "};\n"
    "\n"
    "struct Expr_Table\n"
    "{\n"
    "};\n"
    "\n"
    "struct Expr\n"
    "{\n"
    "};\n"
    "\n"
    "struct Expr_Bin\n"
    "{\n"
    "  enum Op_Bin op;\n"
    "  Expr_ID x;\n"
    "  Expr_ID y;\n"
    "};\n"
#endif
    "\n"
    "/*<< *.c >>*/\n"
    "// ${BANNER}\n"
  );
  STACK = _prev_stack;
}
