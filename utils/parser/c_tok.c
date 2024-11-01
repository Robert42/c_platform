// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

char* c_tok_parse_str_lit(Mem_Region* region, const char** code)
{
  debug_assert_ptr_ne(code, NULL);
  debug_assert_ptr_ne(*code, NULL);

  debug_assert_char_eq(**code, '"'); // not a c string literal

  char* result = (char*)region->begin;

  const char* curr = *code;
  ++curr; // skip leading '"'
  while(true)
  {
    switch(*curr)
    {
    case 0:
      PANIC("Unterminated string literal");
    case '\\':
      curr++;
      switch(*curr)
      {
      case '"':
      case '\\':
        *MEM_REGION_ALLOC(region, char) = *curr;
        curr++;
        break;
      case 'n':
        *MEM_REGION_ALLOC(region, char) = '\n';
        curr++;
        break;
      default:
        UNIMPLEMENTED("Unknown c string escape code");
      }
      continue;
    case '"':
    {
      *MEM_REGION_ALLOC(region, char) = 0;
      ++curr; // skip tailing '"'
      *code = curr;
      return result;
    }
    default:
      *MEM_REGION_ALLOC(region, char) = *curr;
      curr++;
    }
  }
}

void c_tok_fmt_cstr_lit(Fmt* f, const char* content)
{
  fmt_write(f, "\"");
  while(*content != 0)
  {
    const char x = *(content++);
    switch(x)
    {
    case 0: UNREACHABLE();
    case '"':
      fmt_write(f, "\\\"");
      break;
    case '\\':
      fmt_write(f, "\\\\");
      break;
    case '\n':
      fmt_write(f, "\\n");
      break;
    default:
      if(x < 31)
        UNIMPLEMENTED();
      fmt_write(f, "%c", x);
    }
  }
  fmt_write(f, "\"");
}

str tok_skip_ident(const char** code)
{
  const char* begin = *code;
  while(true)
  {
    switch(**code)
    {
    case '_':
    case '0' ... '9':
    case 'A' ... 'Z':
    case 'a' ... 'z':
      ++*code;
      continue;
    default:
      return (str){begin, *code};
    }
  }
}

