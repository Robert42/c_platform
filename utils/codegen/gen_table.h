// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct Autogen_ADT_Column_Field;
struct Autogen_ADT_Column;
struct Autogen_ADT;

struct Autogen_ADT
{
  const char* name;

  struct Autogen_ADT_Variant* variants;
  usize num_variants;

  struct Autogen_ADT_MetaData* metadata;
  usize num_metadata;
};

struct Autogen_ADT_Variant
{
  const char* name;

  struct Autogen_ADT_Field* fields;
  usize num_fields;
};

struct Autogen_ADT_MetaData
{
  const char* name;

  struct Autogen_ADT_Field* fields;
  usize num_fields;
};

struct Autogen_ADT_Field
{
  const char* type;
  const char* name;

  struct
  {
    s16 bits : 11;
    bool integrate_to_id : 1;
  } layout;
};

void _autogen_adt_fmt(Fmt* f_h_decl, Fmt* f_h, Fmt* f_c, struct Autogen_ADT adt);
void autogen_adt(Path dir, struct Autogen_ADT adt);

