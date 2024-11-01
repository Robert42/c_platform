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
  YAML_TOK_IDENT = 'i',
  YAML_TOK_SPACE = ' ',
  YAML_TOK_LINEBREAK = '\n',

  YAML_TOK_LIT_STR = '"',
  YAML_TOK_LIT_INT = '0',

  YAML_COLON = ':',
};

struct Yaml_Token
{
  enum Yaml_Token_ID id;
  union
  {
    str content_str;
    yaml_int content_int;
  };
};

static const char* yaml_tok_id_fmt(enum Yaml_Token_ID tok)
{
  switch(tok)
  {
  X_CASE_RETURN_AS_CSTR(YAML_TOK_DOC_BEGIN)
  X_CASE_RETURN_AS_CSTR(YAML_TOK_DOC_END)
  X_CASE_RETURN_AS_CSTR(YAML_TOK_CONTENT)
  X_CASE_RETURN_AS_CSTR(YAML_TOK_IDENT)
  X_CASE_RETURN_AS_CSTR(YAML_TOK_SPACE)
  X_CASE_RETURN_AS_CSTR(YAML_TOK_LINEBREAK)
  X_CASE_RETURN_AS_CSTR(YAML_TOK_LIT_STR)
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

// ==== yaml_node_fmt ====

static const char* _yaml_flow_fmt(Fmt* f, struct Yaml_Node node)
{
  switch(node.kind)
  {
  case YAML_DICT:
    fmt_write(f, "{");
    for(usize i=0; i<node.content.mapping_dict.len; ++i)
    {
      if(i != 0)
        fmt_write(f, ", ");
      _yaml_flow_fmt(f, node.content.mapping_dict.keys[i]);
      fmt_write(f, ": ");
      _yaml_flow_fmt(f, node.content.mapping_dict.values[i]);
    }
    fmt_write(f, "}");
    break;
  case YAML_LIST:
    fmt_write(f, "[");
    for(usize i=0; i<node.content.seq_list.len; ++i)
    {
      if(i != 0)
        fmt_write(f, ", ");
      _yaml_flow_fmt(f, node.content.seq_list.xs[i]);
    }
    fmt_write(f, "]");
    break;
  case YAML_BOOL:
    fmt_write(f, "%s", node.content.scalar_bool ? "true" : "false");
    break;
  case YAML_INT:
    fmt_write(f, "%" PRI_yaml_int, node.content.scalar_int);
    break;
  case YAML_STR:
    c_tok_fmt_str_lit(f, node.content.scalar_str);
    break;
  }
}

const char* yaml_node_fmt(Mem_Region* region, struct Yaml_Node node)
{
  Fmt f = fmt_new_from_region(region, 4096);
  _yaml_flow_fmt(&f, node);
  return f.begin;
}

// ==== yaml_lex ====

#define TOK(X, ...) ((struct Yaml_Token){.id = (X), __VA_ARGS__})

struct Yaml_Token yaml_lex(Mem_Region* region, const char** code)
{
  const char* begin = *code;
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
  case '"':
  {
    const char* xs = c_tok_parse_str_lit(region, code);
    return TOK(YAML_TOK_LIT_STR, .content_str=str_from_cstr(xs));
  }
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
  case '0' ... '9':
  {
    yaml_int x = 0;
    while(**code)
      switch(**code)
      {
      case '0' ... '9':
        x *= 10;
        x += **code - '0';
        *code += 1;
        continue;
      default:
      {
        const str span = {begin, *code};
        return TOK(YAML_TOK_LIT_INT, .content_int=x);
      }
      }
  }
  case '_':
  case 'a' ... 'z':
  case 'A' ... 'Z':
    while(**code)
      switch(**code)
      {
      case '-':
      case '_':
      case '0' ... '9':
      case 'a' ... 'z':
      case 'A' ... 'Z':
        *code += 1;
        continue;
      default:
      {
        const str span = {begin, *code};
        return TOK(YAML_TOK_IDENT, .content_str=span);
      }
      }
  default:
    break;
  }

  *code += 1;
  return TOK(YAML_TOK_CONTENT);
}
#undef TOK

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

struct Yaml_Tokenizer
{
  Mem_Region* region;
  const char* code;
  struct Yaml_Token next, peek;
};

static struct Yaml_Tokenizer _yaml_tokenize_start(struct Yaml_Parse_Context* ctx, const char* code)
{
  Mem_Region* const region = ctx->region;
  struct Yaml_Tokenizer tokenizer = {
    .region = region,
    .code = code,
  };

  tokenizer.peek = yaml_lex(tokenizer.region, &tokenizer.code);

  return tokenizer;
}

static struct Yaml_Token _yaml_tokenize_next(struct Yaml_Tokenizer* tokenizer)
{
  struct Yaml_Token next = tokenizer->peek;
  tokenizer->peek = yaml_lex(tokenizer->region, &tokenizer->code);
  return next;
}

void _yaml_tokenize_skip_whitespace(struct Yaml_Tokenizer* tokenizer)
{
  while(_yaml_is_space(tokenizer->peek.id))
    _yaml_tokenize_next(tokenizer);
}

static struct Yaml_Node _yaml_parse_flow(struct Yaml_Tokenizer* tokenizer)
{
  switch(tokenizer->peek.id)
  {
  case YAML_TOK_LIT_INT:
  {
    struct Yaml_Token tok = _yaml_tokenize_next(tokenizer);

    return (struct Yaml_Node){
      .kind = YAML_INT,
      .content.scalar_int = tok.content_int,
    };
  }
  default:
    TODO();
  }
}

static struct Yaml_Node _yaml_parse_dict_block(struct Yaml_Tokenizer* tokenizer)
{
  struct Yaml_Node dict = {
    .kind = YAML_DICT,
  };

  while(true)
  {
    switch(tokenizer->peek.id)
    {
    case YAML_COLON:
      _yaml_tokenize_next(tokenizer);
      dict.content.mapping_dict.len++;
      continue;
    case YAML_TOK_DOC_END:
    case YAML_TOK_DOC_BEGIN:
      return dict;
    case YAML_TOK_LIT_INT:
      if(dict.content.mapping_dict.len == 0) // TODO: build a proper dict
      return _yaml_parse_flow(tokenizer);
    default:
      _yaml_tokenize_next(tokenizer);
      continue;
    }
  }
  
  UNREACHABLE();
}

struct Yaml_Node yaml_parse_doc_with_rest(Mem_Region* region, const char** code)
{
  struct Yaml_Parse_Context ctx;
  ctx.region = region;

  struct Yaml_Tokenizer tokenizer = _yaml_tokenize_start(&ctx, *code);

  _yaml_tokenize_skip_whitespace(&tokenizer);
  if(tokenizer.peek.id == YAML_TOK_DOC_BEGIN)
    tokenizer.peek.id = YAML_TOK_SPACE;

  struct Yaml_Node node = _yaml_parse_dict_block(&tokenizer);

  *code = tokenizer.code;

  return node;
}

struct Yaml_Node yaml_parse_doc(Mem_Region* region, const char* code)
{
  return yaml_parse_doc_with_rest(region, &code);
}

