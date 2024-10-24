// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

enum Ini_Format_Field_Type
{
  INI_FIELD_TYPE_BOOL, // bool
  INI_FIELD_TYPE_USIZE, // usize
  INI_FIELD_TYPE_CSTR, // char*
  INI_FIELD_TYPE_CSTR_ARRAY, // char**, usize
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

