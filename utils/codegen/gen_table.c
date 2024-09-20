// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "gen_table.h"

const char* const BANNER = "// ${BANNER}\n";

void _autogen_multi_table_fmt(Fmt* f_h_decl, Fmt* f_h, Fmt* f_c, struct Autogen_Multi_Table multi_table)
{
  fmt_write(f_h_decl, "%s", BANNER);
  fmt_write(f_h, "%s", BANNER);
  fmt_write(f_c, "%s", BANNER);

  fmt_write(f_h_decl, "enum %s_Variant;\n", multi_table.name);
  fmt_write(f_h_decl, "struct %s_ID;\n", multi_table.name);
  fmt_write(f_h_decl, "struct %s;\n", multi_table.name);
}

void autogen_multi_table(Path dir, struct Autogen_Multi_Table multi_table)
{
  const Mem_Region _prev_stack = STACK;

  Fmt f_h_decl = fmt_new_from_region(&STACK, 5*MiB);
  Fmt f_h = fmt_new_from_region(&STACK, 5*MiB);
  Fmt f_c = fmt_new_from_region(&STACK, 5*MiB);

  _autogen_multi_table_fmt(&f_h_decl, &f_h, &f_c, multi_table);

  const char* name_lower = cstr_to_lower(&STACK, multi_table.name);
  file_text_create_from_cstr_if_different(path_join_cstr_append_cstr(dir, name_lower, ".decl.h"), f_h_decl.begin);
  file_text_create_from_cstr_if_different(path_join_cstr_append_cstr(dir, name_lower, ".h"), f_h.begin);
  file_text_create_from_cstr_if_different(path_join_cstr_append_cstr(dir, name_lower, ".c"), f_c.begin);

  STACK = _prev_stack;
}
