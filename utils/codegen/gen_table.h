// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct Autogen_Table_Column_Field;
struct Autogen_Table_Column;
struct Autogen_Table;

struct Autogen_Table
{
  const char* name;

  struct Autogen_Table_Variant* variants;
  usize num_variants;

  struct Autogen_Table_MetaData* metadata;
  usize num_metadata;
};

struct Autogen_Table_Variant
{
  const char* name;

  struct Autogen_Table_Field* fields;
  usize num_fields;
};

struct Autogen_Table_MetaData
{
  const char* name;

  struct Autogen_Table_Field* fields;
  usize num_fields;
};

struct Autogen_Table_Field
{
  const char* type;
  const char* name;

  struct
  {
    s16 bits : 11;
    bool integrate_to_id : 1;
  } layout;
};

void _autogen_table_fmt(Fmt* f_h_decl, Fmt* f_h, Fmt* f_c, struct Autogen_Table table);
void autogen_table(Path dir, struct Autogen_Table table);

