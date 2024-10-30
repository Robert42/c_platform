// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "yaml.h"

#define TEST_YAML_LEX(CODE, REST, TOK) \
  { \
    const char* code = (CODE REST); \
    assert_yaml_tok_eq(yaml_lex(&code), TOK); \
    assert_cstr_eq(code, REST); \
  }

void yaml_test()
{
  const Mem_Region _prev = STACK;

  // ==== YAML lexer ====
  TEST_YAML_LEX(":", "-", YAML_TOK_CONTENT);
  TEST_YAML_LEX("-", "-", YAML_TOK_CONTENT);

  TEST_YAML_LEX(":", " ", YAML_COLON);
  TEST_YAML_LEX(":", "\n", YAML_COLON);
  TEST_YAML_LEX("---", " ", YAML_TOK_DOC_BEGIN);
  TEST_YAML_LEX("...", " ", YAML_TOK_DOC_END);

  // ==== YAML dictionaties ====

  // empty
  {
    const char* full = "";
    const char* xs = full;
    struct Yaml_Node root = yaml_parse_doc_with_rest(&STACK, &xs);

    assert_ptr_eq(xs, full);
    assert(root.kind == YAML_DICT);
    assert_usize_eq(root.content.mapping_dict.len, 0);
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
    assert_usize_eq(root.content.mapping_dict.len, 3);
  }

  // ==== YAML documents ====

  // first doc is empty
  {
    const char* full = 
      "...\n"
      "---\n"
      "name: John Doe\n"
      "hero: true\n"
      "age: 42\n"
      "...\n"
    ;
    const char* xs = full;
    struct Yaml_Node root = yaml_parse_doc_with_rest(&STACK, &xs);

    assert_ptr_eq(xs, full+3);
    assert(root.kind == YAML_DICT);
    assert_usize_eq(root.content.mapping_dict.len, 0);
    
    root = yaml_parse_doc_with_rest(&STACK, &xs);

    assert_ptr_eq(xs, full+strlen(full)-1);
    assert(root.kind == YAML_DICT);
    assert_usize_eq(root.content.mapping_dict.len, 3);
    
    root = yaml_parse_doc_with_rest(&STACK, &xs);

    assert_ptr_eq(xs, full+strlen(full));
    assert(root.kind == YAML_DICT);
    assert_usize_eq(root.content.mapping_dict.len, 0);
  }
  
  // Use `---` as separator
  {
    const char* full = 
      "---\n"
      "name: John Doe\n"
      "---\n"
      "hero: true\n"
      "age: 42\n"
    ;

    const char* xs = full;
    struct Yaml_Node root = yaml_parse_doc_with_rest(&STACK, &xs);

    assert(root.kind == YAML_DICT);
    assert_usize_eq(root.content.mapping_dict.len, 1);
    
    root = yaml_parse_doc_with_rest(&STACK, &xs);

    assert(root.kind == YAML_DICT);
    assert_usize_eq(root.content.mapping_dict.len, 2);
    
    root = yaml_parse_doc_with_rest(&STACK, &xs);

    assert(root.kind == YAML_DICT);
    assert_usize_eq(root.content.mapping_dict.len, 0);
  }

  STACK = _prev;
}

#undef TEST_YAML_LEX

