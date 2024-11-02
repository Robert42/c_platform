// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "yaml.h"

#define TEST_YAML_LEX(CODE, REST, TOK) \
  { \
    const char* code = (CODE REST); \
    struct Yaml_Token tok = yaml_lex(&STACK, &code); \
    assert_yaml_tok_id_eq(tok.id, TOK); \
    assert_cstr_eq(code, REST); \
  }
#define TEST_YAML_LEX_STR(CODE, REST, TOK, CONTENT) \
  { \
    const char* code = (CODE REST); \
    struct Yaml_Token tok = yaml_lex(&STACK, &code); \
    assert_yaml_tok_id_eq(tok.id, TOK); \
    assert_cstr_eq(code, REST); \
    assert_str_eq(tok.content_str, STR_LIT(CONTENT)); \
  }
#define TEST_YAML_PARSE_FMT(CODE, REST, KIND, FMT) \
  { \
    const char* code = (CODE REST); \
    struct Yaml_Node node = yaml_parse_doc_with_rest(&STACK, &code); \
    assert_usize_eq(node.kind, KIND); \
    assert_cstr_eq(yaml_node_fmt(&STACK, node), FMT); \
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

  TEST_YAML_LEX_STR("\"\"", " ", YAML_TOK_LIT_STR, "");
  TEST_YAML_LEX_STR("\"x\\ny\\\\z\"", " ", YAML_TOK_LIT_STR, "x\ny\\z");

  TEST_YAML_LEX_STR("_3D-stuff", " ", YAML_TOK_IDENT, "_3D-stuff");
  TEST_YAML_LEX_STR("hello-world", " ", YAML_TOK_IDENT, "hello-world");
  TEST_YAML_LEX_STR("HELLO_WORLD", " ", YAML_TOK_IDENT, "HELLO_WORLD");

  // ==== YAML fmt ====
  {
    struct Yaml_Node xs = {
      .kind = YAML_STR,
      .content.scalar_str = STR_LIT("newline=`\n` backslash=`\\`"),
    };

    assert_cstr_eq(yaml_node_fmt(&STACK, xs), "\"newline=`\\n` backslash=`\\\\`\"");
  }
  {
    struct Yaml_Node xs[] = {
      {
        .kind = YAML_INT,
        .content.scalar_int = 42,
      },
      {
        .kind = YAML_BOOL,
        .content.scalar_bool = true,
      },
      {
        .kind = YAML_INT,
        .content.scalar_int = 137,
      },
      {
        .kind = YAML_LIST,
      },
      {
        .kind = YAML_BOOL,
        .content.scalar_bool = false,
      },
    };
    struct Yaml_Node x = {
      .kind = YAML_LIST,
      .content.seq_list = {
        .xs = xs,
        .len = ARRAY_LEN(xs),
      },
    };

    assert_cstr_eq(yaml_node_fmt(&STACK, x), "[42, true, 137, [], false]");
  }
  {
    struct Yaml_Node keys[] = {
      {
        .kind = YAML_STR,
        .content.scalar_str = STR_LIT("name"),
      },
      {
        .kind = YAML_STR,
        .content.scalar_str = STR_LIT("age"),
      },
    };
    struct Yaml_Node values[] = {
      {
        .kind = YAML_STR,
        .content.scalar_str = STR_LIT("John Doe"),
      },
      {
        .kind = YAML_INT,
        .content.scalar_int = 42,
      },
    };
    struct Yaml_Node x = {
      .kind = YAML_DICT,
      .content.mapping_dict = {
        .keys = keys,
        .values = values,
        .len = ARRAY_LEN(keys),
      },
    };

    assert_cstr_eq(yaml_node_fmt(&STACK, x), "{\"name\": \"John Doe\", \"age\": 42}");
  }

  // ==== YAML scalars ====

  TEST_YAML_PARSE_FMT("42", "  ", YAML_INT, "42");

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
#undef TEST_YAML_LEX_STR
#undef TEST_YAML_PARSE_FMT

