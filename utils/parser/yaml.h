// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

// YAML subset. No support for
// - UTF-16 nor UTF-32 encoded files
// - 

enum Yaml_Kind
{
  // mapping
  YAML_DICT,

  // sequence
  YAML_LIST,

  // scalars
  YAML_BOOL,
  YAML_INT,
  YAML_STR,
};

struct Yaml_Node;

struct Yaml_Dict
{
  struct Yaml_Node* keys;
  struct Yaml_Node* values;
  usize len;
};

struct Yaml_List
{
  struct Yaml_Node* xs;
  usize len;
};

#define PRI_yaml_int PRId64
typedef s64 yaml_int;

struct Yaml_Node
{
  enum Yaml_Kind kind;
  union
  {
    struct Yaml_Dict mapping_dict;

    struct Yaml_List seq_list;

    bool scalar_bool;
    yaml_int scalar_int;
    str scalar_str;
  } content;
};

struct Yaml_Node yaml_parse_doc_with_rest(Mem_Region* region, const char** code);
struct Yaml_Node yaml_parse_doc(Mem_Region* region, const char* code);

