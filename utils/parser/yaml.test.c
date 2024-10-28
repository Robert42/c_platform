// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "yaml.h"

void yaml_test()
{
  const Mem_Region _prev = STACK;

  // ==== YAML dictionaties ====

  // empty
  {
    const char* full = "";
    const char* xs = full;
    struct Yaml_Node root = yaml_parse_doc_with_rest(&STACK, &xs);

    assert_ptr_eq(xs, full);
    assert(root.kind == YAML_DICT);
    assert(root.content.mapping_dict.len == 0);
  }

  // simple scalars
  {
    const char* full = 
      "name: John Doe\n"
      "hero: true\n"
      "age: 42\n"
    ;
    const char* xs = full;
    struct Yaml_Node root = yaml_parse_doc_with_rest(&STACK, &xs);

    assert_ptr_eq(xs, full+strlen(full));
    assert(root.kind == YAML_DICT);
    assert(root.content.mapping_dict.len == 3);
  }

  // ==== YAML documents ====

  STACK = _prev;
}
