// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "gen_table.h"

const char* test_autogen_table_fmt(Mem_Region* region, const struct Autogen_Table* table, u32 root_idx)
{
  Fmt f_h_decl = fmt_new_from_region(region, 15*MiB);
  Fmt f_h = fmt_new_from_region(region, 5*MiB);
  Fmt f_c = fmt_new_from_region(region, 5*MiB);

  _autogen_table_fmt(&f_h_decl, &f_h, &f_c, table, root_idx);

  fmt_write(&f_h_decl, "\n/*<< *.h >>*/\n%s", f_h.begin);
  fmt_write(&f_h_decl, "\n/*<< *.c >>*/\n%s", f_c.begin);

  return f_h_decl.begin;
}

enum Test_Table_Gen_Node_Expr
{
  TTGE_NODE_EXPR,

  TTGE_NODE_EXPR_BEGIN,
  TTGE_NODE_BIN = TTGE_NODE_EXPR_BEGIN,
  TTGE_NODE_EXPR_END,

  _TTGE_NODE_EXPR_COUNT = TTGE_NODE_EXPR_END,
};

enum Test_Table_Gen_Expr_Leaf
{
  TTGE_EXPR_BIN,
  TTGE_EXPR_END,

  _TTGE_EXPR_TOTAL_COUNT = TTGE_EXPR_END,
};

void gen_table_test()
{
  const Mem_Region _prev_stack = STACK;

  struct Autogen_Table autogen_table = {
    .node_count = _TTGE_NODE_EXPR_COUNT,
    .column_count = _TTGE_EXPR_TOTAL_COUNT,
  };
  autogen_table_alloc(&STACK, &autogen_table);

  autogen_table.nodes[TTGE_NODE_EXPR] = (struct Autogen_Table_ID_Space_Node){
    .name = "Expr",
    .variant = AGTISNV_VARIANTS,
    .payload = TTGE_EXPR_BIN,
    .node.num_subnodes = TTGE_NODE_EXPR_END - TTGE_NODE_EXPR_BEGIN,
    .node.first_sub_node = TTGE_NODE_EXPR_BEGIN,
  };
  autogen_table.nodes[TTGE_NODE_BIN] = (struct Autogen_Table_ID_Space_Node){
    .name = "Bin",
    .variant = AGTISNV_LEAF,
  };

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

  assert_cstr_eq(test_autogen_table_fmt(&STACK, &autogen_table, TTGE_NODE_EXPR),
    "typedef struct {u32 id;} Expr_ID;\n"
    "enum Expr_Variant;\n"
#if 0
    "struct Expr_Table;\n"
    "struct Expr;\n"
    "struct Expr_Bin;\n"
#endif
    "\n"
    "/*<< *.h >>*/\n"
    "enum Expr_Variant\n"
    "{\n"
    "  EXPR_BIN,\n"
    "};\n"
    "\n"
#if 0
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
  );
  STACK = _prev_stack;
}
