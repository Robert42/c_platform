// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "yaml.h"

void yaml_test()
{
  const Mem_Region _prev = STACK;

  // ==== YAML dictionaties ====

  // empty
  {
    const str full = STR_LIT("");
    str xs = full;
    struct Yaml_Node root = yaml_parse_doc_with_rest(&STACK, &xs);

    assert_ptr_eq(xs.begin, full.begin);
    assert_ptr_eq(xs.end, full.end);
    assert(root.kind == YAML_DICT);
    assert(root.content.mapping_dict.len == 0);
  }

  // ==== YAML documents ====

  STACK = _prev;
}
