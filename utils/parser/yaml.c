// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "yaml.h"

struct Yaml_Parse_Context
{
  Mem_Region* region;
};

enum Yaml_Token_ID
{
  YAML_TOK_DOC_END = 0, // `...`
  YAML_TOK_DOC_BEGIN, // `---`
  
  YAML_TOK_CONTENT = 'x',
  YAML_TOK_SPACE = ' ',
  YAML_TOK_LINEBREAK = '\n',

  YAML_COLON = ':',
};

struct Yaml_Token
{
  enum Yaml_Token_ID id;
};

static const char* yaml_tok_id_fmt(enum Yaml_Token_ID tok)
{
  switch(tok)
  {
  X_CASE_RETURN_AS_CSTR(YAML_TOK_DOC_BEGIN)
  X_CASE_RETURN_AS_CSTR(YAML_TOK_DOC_END)
  X_CASE_RETURN_AS_CSTR(YAML_TOK_CONTENT)
  X_CASE_RETURN_AS_CSTR(YAML_TOK_SPACE)
  X_CASE_RETURN_AS_CSTR(YAML_TOK_LINEBREAK)
  X_CASE_RETURN_AS_CSTR(YAML_COLON)
  }
  UNREACHABLE();
}
void __assert_yaml_tok_id_eq__(enum Yaml_Token_ID x, enum Yaml_Token_ID y, const char* condition, const char* file, int line)
{
  if(LIKELY(x == y))
    return;
  else
  __bin_assert_failed__(condition, yaml_tok_id_fmt(x), yaml_tok_id_fmt(y), file, line);
}
#define assert_yaml_tok_id_eq(x, y) __assert_yaml_tok_id_eq__(x, y, #x " == " #y, __FILE__, __LINE__)

#define TOK(X) ((struct Yaml_Token){.id = (X)})

struct Yaml_Token yaml_lex(const char** code)
{
  switch((*code)[0])
  {
  case 0:
    return TOK(YAML_TOK_DOC_END);
  case ' ':
    while(**code == ' ')
      *code += 1;

    return TOK(YAML_TOK_SPACE);
  case '\n':
    *code += 1;
    return TOK(YAML_TOK_LINEBREAK);
  case ':':
    if(char_is_ws((*code)[1]))
    {
      *code += 1;
      return TOK(YAML_COLON);
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
        return TOK(YAML_TOK_DOC_BEGIN);
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
        return TOK(YAML_TOK_DOC_END);
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
  return TOK(YAML_TOK_CONTENT);
}

static bool _yaml_is_inline_space(enum Yaml_Token_ID tok)
{
  switch(tok)
  {
  case YAML_TOK_SPACE:
    return true;
  default:
    return false;
  }
}

static bool _yaml_is_space(enum Yaml_Token_ID tok)
{
  switch(tok)
  {
  case YAML_TOK_LINEBREAK:
    return true;
  default:
    return _yaml_is_inline_space(tok);
  }
}

static struct Yaml_Node _yaml_parse_dict_block(struct Yaml_Parse_Context* ctx, const char** code)
{
  struct Yaml_Node dict = {
    .kind = YAML_DICT,
  };

  struct Yaml_Token peek = yaml_lex(code);
  while(_yaml_is_space(peek.id))
    peek = yaml_lex(code);
  if(peek.id == YAML_TOK_DOC_BEGIN)
    peek = TOK(YAML_TOK_SPACE);

  while(peek.id != YAML_TOK_DOC_END)
  {
    struct Yaml_Token next = peek;
    peek = yaml_lex(code);
    switch(next.id)
    {
    case YAML_COLON:
      dict.content.mapping_dict.len++;
      break;
    case YAML_TOK_DOC_END:
    case YAML_TOK_DOC_BEGIN:
      return dict;
    }
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

#undef TOK
