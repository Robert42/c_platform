// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct Autogen_Table_Column;
struct Autogen_Table;
struct Autogen_Multi_Table;

// A Multitable is a collection of tables.
// The tables shared the ID type, and can can have both distinct and shared columns.
struct Autogen_Multi_Table
{
  const char* name;

  struct Autogen_Table* distinct_tables;
  u32 num_distinct;

  u32 num_shared;
  struct Autogen_Table* shared_tables;

  u32 shared_is_metadata; // bitfield indexing shared_tables (meaning it will be excluded when table rows for equality)
};

struct Autogen_Table
{
  const char* name;

  struct Autogen_Table_Column* columns;
  u32 num_columns;
};

struct Autogen_Table_Column
{
  const char* type;
  const char* name;

  struct
  {
    s16 bits : 11;
    bool integrate_to_id : 1;
  } layout;
};

void _autogen_multi_table_fmt(Fmt* f_h_decl, Fmt* f_h, Fmt* f_c, struct Autogen_Multi_Table multi_table);
void autogen_multi_table(Path dir, struct Autogen_Multi_Table multi_table);

