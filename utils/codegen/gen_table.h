// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct Autogen_Table_Column;
struct Autogen_Table;

enum Autogen_Table_ID_Space_Node_Variant
{
  AGTISNV_LEAF,
  AGTISNV_LAYERS,
  AGTISNV_VARIANTS,
  AGTISNV_META_DATA,
  AGTISNV_SHARED_DATA,
};

// A Multitable is a collection of tables, that share the ID space
// The tables shared the ID type, and can can have both distinct and shared columns.
struct Autogen_Table
{
  struct Autogen_Table_ID_Space_Node
  {
    const char* name;
    enum Autogen_Table_ID_Space_Node_Variant variant : 3;
    u32 payload : 29;

    union
    {
      struct
      {
        u32 num_subnodes;
        u32 first_sub_node;
      } leaf;
      
      struct
      {
        u32 num_columns;
        u32 first_column;
      } node;
    };
  };

  struct Autogen_Table_ID_Space_Node* nodes;
  struct Autogen_Table_Column* columns;
  u32 total_num_nodes;
  u32 total_num_columns;
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

void _autogen_table_fmt(Fmt* f_h_decl, Fmt* f_h, Fmt* f_c, struct Autogen_Table table);
void autogen_table(Path dir, struct Autogen_Table table);

