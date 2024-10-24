// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "ini.h"

static const char* _ini_parse_str(Mem_Region* region, const char** code);

void ini_parse(Mem_Region* region, const struct Ini_Format* format, const char* code)
{
  const struct Ini_Format_Section* curr_section_format = NULL;
  void* curr_section_data = NULL;
  while(true)
  {
    switch(code[0])
    {
    case 0:
      return;
    case '[':
    {
      code = cstr_trim_left(code + 1);
      const char* const begin = code;
      const char* end = strchr(begin, ']');
      code = end+1;
      assert_char_eq(code[0], '\n');
      code++;

      const str name = str_trim_right((str){begin, end});

      curr_section_format = NULL;
      for(usize i=0; i<format->num_sections; ++i)
        if(str_cstr_cmp(name, format->section_formats[i].name) == 0)
          curr_section_format = &format->section_formats[i];

      if(curr_section_format == NULL)
        PANIC("ini_parse: unexpected section `[%s]`", str_fmt(name));

      const usize section_data_idx = (*curr_section_format->num_sections_read)++;
      assert_usize_lt(section_data_idx, curr_section_format->section_data_capacity);
      curr_section_data = curr_section_format->section_data + section_data_idx * curr_section_format->section_entry_size;
      break;
    }
    case '_':
    case 'a' ... 'z':
    case 'A' ... 'Z':
    {
      assert_ptr_ne(curr_section_format, NULL); // not inside section
      str field_name = tok_skip_ident(&code);

      code = cstr_trim_left(code);
      assert_char_eq(*code, '=');
      code = cstr_trim_left(code+1);

      const struct Ini_Format_Field* field_format = NULL;
      for(usize i=curr_section_format->field_begin; i<curr_section_format->field_end; ++i)
        if(str_cstr_cmp(field_name, format->field_formats[i].name) == 0)
          field_format = &format->field_formats[i];
      if(field_format == NULL)
        PANIC("ini_parse: unexpected field `%s` in section `[%s]`", str_fmt(field_name), curr_section_format->name);

      void* const field_data = curr_section_data + field_format->field_offset;
      switch(field_format->type)
      {
      case INI_FIELD_TYPE_BOOL:
      {
        str ident = tok_skip_ident(&code);
        bool* val = (bool*)field_data;
        if(str_cmp(ident, STR_LIT("true")) == 0)
          *val = true;
        else if(str_cmp(ident, STR_LIT("false")) == 0)
          *val = false;
        else
          PANIC("Not a bool literal `%s`", str_fmt(ident));
        break;
      }
      case INI_FIELD_TYPE_USIZE:
        *(usize*)field_data = cstr_to_usize(&code);
        break;
      case INI_FIELD_TYPE_CSTR:
        *(const char**)field_data = _ini_parse_str(region, &code);
        break;
      case INI_FIELD_TYPE_CSTR_ARRAY:
      {
        const char* xs[4096];
        usize len = 0;

        while(*code != '\n' && *code != 0)
        {
          assert_usize_lt(len, ARRAY_LEN(xs));
          xs[len++] = _ini_parse_str(region, &code);
        }
        
        *(const char***)field_data = MEM_REGION_COPY_ARRAY(region, const char*, xs, len);
        *(usize*)(field_data + sizeof(void*)) = len;
        break;
      }
      }
      code = cstr_trim_left(code);
      continue;
    }
    case '\n':
      code++;
      continue;
    default:
      UNIMPLEMENTED();
    }
  }
}

char* ini_fmt(Mem_Region* region, const struct Ini_Format* format)
{
  Fmt f = fmt_new_from_region(region, 4096);

  for(usize section_format_idx=0; section_format_idx < format->num_sections; ++section_format_idx)
  {
    const struct Ini_Format_Section* const section_format = &format->section_formats[section_format_idx];
    void* section_data = section_format->section_data;
    for(usize section_idx=0; section_idx < *section_format->num_sections_read; ++section_idx)
    {
      if(f.begin != f.end)
        fmt_write(&f, "\n");
      fmt_write(&f, "[%s]\n", section_format->name);

      for(usize field_format_idx=section_format->field_begin; field_format_idx < section_format->field_end; ++field_format_idx)
      {
        const struct Ini_Format_Field* const field_format = &format->field_formats[field_format_idx];
        const void* data = section_data + field_format->field_offset;

        fmt_write(&f, "%s = ", field_format->name);
        switch(field_format -> type)
        {
        case INI_FIELD_TYPE_BOOL: // bool
          fmt_write(&f, "%s", *(bool*)data ? "true" : "false");
          break;
        case INI_FIELD_TYPE_USIZE: // usize
          fmt_write(&f, "%zu", *(usize*)data);
          break;
        case INI_FIELD_TYPE_CSTR: // char*
          c_tok_fmt_str_lit(&f, *(const char**)data);
          break;
        case INI_FIELD_TYPE_CSTR_ARRAY: // char**, usize
        {
          const char** xs = *(const char***)data;
          const usize len = *(const usize*)(data + sizeof(void*));

          if(len == 0)
          {
            f.end[-1] = 0;
            f.end--;
          }
          else
            for(usize i=0; i<len; ++i)
            {
              if(i!=0)
                fmt_write(&f, " ");
              c_tok_fmt_str_lit(&f, xs[i]);
            }
          break;
        }
        }
        fmt_write(&f, "\n");
      }
      section_data += section_format->section_entry_size;
    }
  }
  return f.begin;
}

static const char* _ini_parse_str(Mem_Region* region, const char** code)
{
  while(**code == ' ')
    ++*code;
  if(**code == '"')
    return c_tok_parse_str_lit(region, code);

  const char* begin = *code;
  while(**code != 0 && !char_is_ws(**code))
    ++*code;
  const char* end = *code;

  return str_fmt_to_region(region, (str){begin, end});
}
