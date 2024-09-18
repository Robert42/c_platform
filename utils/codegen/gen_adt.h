// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct Autogen_Adt_Column_Field;
struct Autogen_Adt_Column;
struct Autogen_Adt;

struct Autogen_Adt
{
  const char* name;

  struct Autogen_Adt_Column* columns;
  usize num_columns;
};

struct Autogen_Adt_Column
{
  const char* name;

  struct Autogen_Adt_Column* fields;
  usize num_fields;
};

struct Autogen_Adt_Column_Field
{
  const char* type;
  const char* name;

  struct
  {
    s16 bits : 11;
    bool integrate_to_id : 1;
  } layout;
};

void _autogen_adt_fmt(Fmt* f_h_decl, Fmt* f_h, Fmt* f_c, struct Autogen_Adt adt);
void autogen_adt(Path dir, struct Autogen_Adt adt);

