// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "yaml.h"

struct Yaml_Parse_Context
{
  Mem_Region* region;
};

static struct Yaml_Node _yaml_parse_dict_block(struct Yaml_Parse_Context* ctx, const char** code)
{
  struct Yaml_Node dict = {
    .kind = YAML_DICT,
  };

  while(**code != 0)
  {
    if(**code == '-')
      dict.content.mapping_dict.len++;
    *code += 1;
  }
  
  return dict;
}

struct Yaml_Node yaml_parse_doc_with_rest(Mem_Region* region, const char** code)
{
  struct Yaml_Parse_Context ctx;
  ctx.region = region;
  return _yaml_parse_dict_block(&ctx, code);
}

struct Yaml_Node yaml_parse_doc(Mem_Region* region, const char* code)
{
  return yaml_parse_doc_with_rest(region, &code);
}

