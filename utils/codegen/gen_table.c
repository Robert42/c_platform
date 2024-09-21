// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "gen_table.h"

extern const char* const BANNER;

struct Autogen_Table_Fmt_Context
{
  Fmt* f_h_decl;
  Fmt* f_h;
  Fmt* f_c;
  const struct Autogen_Table* table;
  
  const char** names_upper;
};

void _autogen_table_fmt_node(struct Autogen_Table_Fmt_Context ctx, u32 node_idx)
{
  debug_assert_usize_lt(node_idx, ctx.table->node_count);

  switch(ctx.table->nodes[node_idx].variant)
  {
  case AGTISNV_LEAF:
    TODO();
    break;
  case AGTISNV_LAYERS:
    TODO();
    break;
  case AGTISNV_VARIANTS:
  {
    const char* name = ctx.table->nodes[node_idx].name;
    fmt_write(ctx.f_h_decl, "enum %s_Variant;\n", name);
    fmt_write(ctx.f_h, "enum %s_Variant\n", name);
    fmt_write(ctx.f_h, "{\n");
    ctx.f_h->indent++;

    u32 sub_nodes_begin = ctx.table->nodes[node_idx].node.first_sub_node;
    u32 sub_nodes_end = sub_nodes_begin + ctx.table->nodes[node_idx].node.num_subnodes;
    for(u32 sub_idx=sub_nodes_begin; sub_idx<sub_nodes_end; ++sub_idx)
    {
      // TODO: stack names? EXPR_LIT_INT where we have a variant Lit and a secondaru variant Int, ...
      fmt_write(ctx.f_h, "%s_%s,\n", ctx.names_upper[node_idx], ctx.names_upper[sub_idx]);
      // ctx.table->nodes[node_idx].name
    }

    ctx.f_h->indent--;
    fmt_write(ctx.f_h, "};\n");
    fmt_write(ctx.f_h, "\n");
    break;
  }
  case AGTISNV_META_DATA:
    TODO();
    break;
  case AGTISNV_SHARED_DATA:
    TODO();
    break;
  }
}

#if 0 // TODO
void _autogen_table_fmt(struct Autogen_Table_Fmt_Context ctx, const struct Autogen_Table* table)
{
  fmt_write(ctx.f_h_decl, "typedef struct _struct_%s_ID %s_ID;\n", table.name, table.name);
  fmt_write(ctx.f_h, "struct _struct_%s_ID\n", table.name);
  fmt_write(ctx.f_h, "{\n");
  f_h->indent++;
  // TODO
  f_h->indent--;
  fmt_write(ctx.f_h, "};\n");
  fmt_write(ctx.f_h, "\n");

  fmt_write(ctx.f_h_decl, "struct %s_Table;\n", table.name);
  fmt_write(ctx.f_h, "struct %s_Table\n", table.name);
  fmt_write(ctx.f_h, "{\n");
  f_h->indent++;
  // TODO
  f_h->indent--;
  fmt_write(ctx.f_h, "};\n");
  fmt_write(ctx.f_h, "\n");

  fmt_write(ctx.f_h_decl, "struct %s;\n", table.name);
  fmt_write(ctx.f_h, "struct %s\n", table.name);
  fmt_write(ctx.f_h, "{\n");
  f_h->indent++;
  // TODO
  f_h->indent--;
  fmt_write(ctx.f_h, "};\n");
  fmt_write(ctx.f_h, "\n");

  for(usize idx_n=0; idx_n<table.node_count; ++idx_n)
  {
    const struct Autogen_Table_ID_Space_Node n = table.nodes[idx_n];

    fmt_write(ctx.f_h_decl, "struct %s_%s;\n", table.name, t.name);
    fmt_write(ctx.f_h, "struct %s_%s\n", table.name, t.name);
    fmt_write(ctx.f_h, "{\n");
    f_h->indent++;
    for(usize idx_c=0; idx_c<t.num_columns; ++idx_c)
    {
      const struct Autogen_Table_Column c = t.columns[idx_c];
      fmt_write(ctx.f_h, "%s %s;\n", c.type, c.name);
    }
    f_h->indent--;
    fmt_write(ctx.f_h, "};\n");
  }
}
#endif

void _autogen_table_fmt(Fmt* f_h_decl, Fmt* f_h, Fmt* f_c, const struct Autogen_Table* table, u32 root_idx)
{
  const Mem_Region _prev_stack = STACK;

  struct Autogen_Table_Fmt_Context ctx = {
    .f_h_decl = f_h_decl,
    .f_h = f_h,
    .f_c = f_c,
    .table = table,
  };

  ctx.names_upper = MEM_REGION_ALLOC_ARRAY(&STACK, const char*, table->node_count);
  for(usize idx_n=0; idx_n<table->node_count; ++idx_n)
  {
    const struct Autogen_Table_ID_Space_Node n = table->nodes[idx_n];
    ctx.names_upper[idx_n] = cstr_to_upper(&STACK, n.name);
  }

  _autogen_table_fmt_node(ctx, root_idx);

  STACK = _prev_stack;
}

void autogen_table(Path dir, const struct Autogen_Table* table, u32 root_idx)
{
  const Mem_Region _prev_stack = STACK;

  Fmt f_h_decl = fmt_new_from_region(&STACK, 5*MiB);
  Fmt f_h = fmt_new_from_region(&STACK, 5*MiB);
  Fmt f_c = fmt_new_from_region(&STACK, 5*MiB);

  fmt_write(&f_h_decl, "%s", BANNER);
  fmt_write(&f_h, "%s", BANNER);
  fmt_write(&f_c, "%s", BANNER);

  _autogen_table_fmt(&f_h_decl, &f_h, &f_c, table, root_idx);

  const char* name_lower = cstr_to_lower(&STACK, table->nodes[root_idx].name);
  file_text_create_from_cstr_if_different(path_join_cstr_append_cstr(dir, name_lower, ".decl.h"), f_h_decl.begin);
  file_text_create_from_cstr_if_different(path_join_cstr_append_cstr(dir, name_lower, ".h"), f_h.begin);
  file_text_create_from_cstr_if_different(path_join_cstr_append_cstr(dir, name_lower, ".c"), f_c.begin);

  STACK = _prev_stack;
}

void autogen_table_alloc(Mem_Region* region, struct Autogen_Table* table)
{
  assert_usize_lt(0, table->node_count);
  assert_usize_lt(0, table->column_count);
  table->nodes = MEM_REGION_ALLOC_ARRAY(region, struct Autogen_Table_ID_Space_Node, table->node_count);
  table->columns = MEM_REGION_ALLOC_ARRAY(region, struct Autogen_Table_Column, table->column_count);
}

