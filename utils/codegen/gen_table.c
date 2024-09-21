// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "gen_table.h"

extern const char* const BANNER;

void _autogen_table_fmt(Fmt* f_h_decl, Fmt* f_h, Fmt* f_c, struct Autogen_Table table)
{
  const Mem_Region _prev_stack = STACK;

  const char** NAMES = MEM_REGION_ALLOC_ARRAY(&STACK, const char*, table.total_num_nodes);
  for(usize idx_n=0; idx_n<table.total_num_nodes; ++idx_n)
  {
    const struct Autogen_Table_ID_Space_Node n = table.nodes[idx_n];
    NAMES[idx_n] = cstr_to_upper(&STACK, n.name);
  }

  fmt_write(f_h_decl, "%s", BANNER);
  fmt_write(f_h, "%s", BANNER);
  fmt_write(f_c, "%s", BANNER);

#if 0
  fmt_write(f_h_decl, "enum %s_Variant;\n", table.name);
  fmt_write(f_h, "enum %s_Variant\n", table.name);
  fmt_write(f_h, "{\n");
  f_h->indent++;
  for(usize idx_n=0; idx_n<table.total_num_nodes; ++idx_n)
    fmt_write(f_h, "%s_%s,\n", NAME, NAMES[idx_n]);
  f_h->indent--;
  fmt_write(f_h, "};\n");
  fmt_write(f_h, "\n");

  fmt_write(f_h_decl, "typedef struct _struct_%s_ID %s_ID;\n", table.name, table.name);
  fmt_write(f_h, "struct _struct_%s_ID\n", table.name);
  fmt_write(f_h, "{\n");
  f_h->indent++;
  // TODO
  f_h->indent--;
  fmt_write(f_h, "};\n");
  fmt_write(f_h, "\n");

  fmt_write(f_h_decl, "struct %s_Table;\n", table.name);
  fmt_write(f_h, "struct %s_Table\n", table.name);
  fmt_write(f_h, "{\n");
  f_h->indent++;
  // TODO
  f_h->indent--;
  fmt_write(f_h, "};\n");
  fmt_write(f_h, "\n");

  fmt_write(f_h_decl, "struct %s;\n", table.name);
  fmt_write(f_h, "struct %s\n", table.name);
  fmt_write(f_h, "{\n");
  f_h->indent++;
  // TODO
  f_h->indent--;
  fmt_write(f_h, "};\n");
  fmt_write(f_h, "\n");

  for(usize idx_n=0; idx_n<table.total_num_nodes; ++idx_n)
  {
    const struct Autogen_Table_ID_Space_Node n = table.nodes[idx_n];

    fmt_write(f_h_decl, "struct %s_%s;\n", table.name, t.name);
    fmt_write(f_h, "struct %s_%s\n", table.name, t.name);
    fmt_write(f_h, "{\n");
    f_h->indent++;
    for(usize idx_c=0; idx_c<t.num_columns; ++idx_c)
    {
      const struct Autogen_Table_Column c = t.columns[idx_c];
      fmt_write(f_h, "%s %s;\n", c.type, c.name);
    }
    f_h->indent--;
    fmt_write(f_h, "};\n");
  }
#endif

  STACK = _prev_stack;
}

void autogen_table(Path dir, struct Autogen_Table table)
{
  const Mem_Region _prev_stack = STACK;

  Fmt f_h_decl = fmt_new_from_region(&STACK, 5*MiB);
  Fmt f_h = fmt_new_from_region(&STACK, 5*MiB);
  Fmt f_c = fmt_new_from_region(&STACK, 5*MiB);

  _autogen_table_fmt(&f_h_decl, &f_h, &f_c, table);

  const char* name_lower = cstr_to_lower(&STACK, table.name);
  file_text_create_from_cstr_if_different(path_join_cstr_append_cstr(dir, name_lower, ".decl.h"), f_h_decl.begin);
  file_text_create_from_cstr_if_different(path_join_cstr_append_cstr(dir, name_lower, ".h"), f_h.begin);
  file_text_create_from_cstr_if_different(path_join_cstr_append_cstr(dir, name_lower, ".c"), f_c.begin);

  STACK = _prev_stack;
}
