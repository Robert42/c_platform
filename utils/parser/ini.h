// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

enum Ini_Format_Field_Type
{
  INI_FIELD_TYPE_BOOL, // bool
  INI_FIELD_TYPE_USIZE, // usize
  INI_FIELD_TYPE_CSTR, // char*
  INI_FIELD_TYPE_CSTR_ARRAY, // char**, usize
};

#define INI_FORMAT_FIELD_TYPE(X) _Generic((X) \
    , bool: INI_FIELD_TYPE_BOOL \
    , usize: INI_FIELD_TYPE_USIZE \
    , const char*: INI_FIELD_TYPE_CSTR \
    , const char**: INI_FIELD_TYPE_CSTR_ARRAY \
  )
#define INI_FORMAT_SECTION_BEGIN(TYPE, NAME, ARRAY, ARRAY_LEN, COUNT_PTR) \
  typedef TYPE Ini_Section_Struct; \
  struct Ini_Format_Section section = { \
    .name = #NAME, \
    .field_begin = ini_format.num_field_types, \
    .field_end = ini_format.num_field_types, \
 \
    .section_data_capacity = ARRAY_LEN, \
    .num_sections_read = COUNT_PTR, \
    .section_data = ARRAY, \
    .section_entry_size = sizeof(Ini_Section_Struct), \
  };
#define INI_FORMAT_SECTION_END() \
  ini_format.section_formats[ini_format.num_sections++] = section; \
  ini_format.num_field_types = section.field_end;
#define INI_FORMAT_FIELD(NAME) \
  ini_format.field_formats[section.field_end++] = (struct Ini_Format_Field){ \
    .name = #NAME, \
    .type = INI_FORMAT_FIELD_TYPE((Ini_Section_Struct){}.NAME), \
    .field_offset = offsetof(Ini_Section_Struct, NAME), \
  };

struct Ini_Format_Section
{
  const char* name;
  u8 field_begin;
  u8 field_end;

  usize section_data_capacity;
  usize* num_sections_read;
  void* section_data;
  usize section_entry_size;
};

struct Ini_Format_Field
{
  const char* name;
  enum Ini_Format_Field_Type type : 8;

  usize field_offset : 12;
};

struct Ini_Format
{
  struct Ini_Format_Field field_formats[255];
  struct Ini_Format_Section section_formats[255];

  u8 num_field_types;
  u8 num_sections;
};

void ini_parse(Mem_Region* region, const struct Ini_Format* format, const char* code);
char* ini_fmt(Mem_Region* region, const struct Ini_Format* format);

