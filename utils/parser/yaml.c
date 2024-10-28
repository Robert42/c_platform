// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "yaml.h"

struct Yaml_Node yaml_parse_doc_with_rest(Mem_Region* region, str* code)
{
  struct Yaml_Node root = {
    .kind = YAML_DICT,
  };
  return root;
}

struct Yaml_Node yaml_parse_doc(Mem_Region* region, str code)
{
  return yaml_parse_doc_with_rest(region, &code);
}

