// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "yaml.h"

struct Yaml_Parse_Context
{
  Mem_Region* region;
};

enum Yaml_Token
{
  YAML_TOK_DOC_BEGIN, // `---`
  YAML_TOK_DOC_END, // `...`
  
  YAML_TOK_CONTENT,

  YAML_COLON = ':',
};

static const char* yaml_tok_fmt(enum Yaml_Token tok)
{
  switch(tok)
  {
  X_CASE_RETURN_AS_CSTR(YAML_TOK_DOC_BEGIN)
  X_CASE_RETURN_AS_CSTR(YAML_TOK_DOC_END)
  X_CASE_RETURN_AS_CSTR(YAML_TOK_CONTENT)
  X_CASE_RETURN_AS_CSTR(YAML_COLON)
  }
  UNREACHABLE();
}
void __assert_yaml_tok_eq__(enum Yaml_Token x, enum Yaml_Token y, const char* condition, const char* file, int line)
{
  if(LIKELY(x == y))
    return;
  else
  __bin_assert_failed__(condition, yaml_tok_fmt(x), yaml_tok_fmt(y), file, line);
}
#define assert_yaml_tok_eq(x, y) __assert_yaml_tok_eq__(x, y, #x " == " #y, __FILE__, __LINE__)

enum Yaml_Token yaml_lex(const char** code)
{
  switch((*code)[0])
  {
  case ':':
    if(char_is_ws((*code)[1]))
    {
      *code += 1;
      return YAML_COLON;
    }
    break;
  case '-':
    switch((*code)[1])
    {
    case '-':
      switch((*code)[2])
      {
      case '-':
        *code += 3;
        return YAML_TOK_DOC_BEGIN;
      default:
        break;
      }
      break;
    default:
      break;
    }
    break;
  case '.':
    switch((*code)[1])
    {
    case '.':
      switch((*code)[2])
      {
      case '.':
        *code += 3;
        return YAML_TOK_DOC_END;
      default:
        break;
      }
      break;
    default:
      break;
    }
    break;
  default:
    break;
  }

  *code += 1;
  return YAML_TOK_CONTENT;
}

static struct Yaml_Node _yaml_parse_dict_block(struct Yaml_Parse_Context* ctx, const char** code)
{
  struct Yaml_Node dict = {
    .kind = YAML_DICT,
  };

  while(**code != 0)
  {
    if(**code == ':')
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

