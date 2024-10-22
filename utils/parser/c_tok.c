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

