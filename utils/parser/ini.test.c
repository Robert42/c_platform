// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "ini.h"

struct Ini_Test_Directory
{
  usize id;

  const char* name;

  usize* sub_ids;
  usize num_sub_ids;
};

struct Ini_Test_File
{
  usize id;

  const char* name;
  const char* content;

  const char** tags;
  usize num_tags;

  bool read_only;
  bool executable;
};

struct Ini_Test_Data
{
  struct Ini_Test_Directory dirs[32];
  struct Ini_Test_File files[32];
  usize dir_count;
  usize file_count;
};

static struct Ini_Format ini_test_format(struct Ini_Test_Data* data);

void ini_test()
{
  struct Ini_Test_Data test_data;

  struct Ini_Format ini_format = ini_test_format(&test_data);

  const char* in =
    "[dir]\n"
    "id = 42\n"
    "name = \"answer of life\"\n"
    "sub_ids = 37 137"
    "\n"
    "[dir]\n"
    "id = 137\n"
    "name = \"the fienstructure constant\"\n"
    "\n"
    "[file]\n"
    "id = 37\n"
    "name = \"most random number (according to polls)\"\n"
    "content = \"Hello, World!\"\n"
    "tags = \"epic drama\" classic \"super\\ncool!\"\n"
    "read_only = true\n";
  const char* expected_out =
    "[dir]\n"
    "id = 42\n"
    "name = \"answer of life\"\n"
    "sub_ids = 37 137"
    "\n"
    "[dir]\n"
    "id = 137\n"
    "name = \"the fienstructure constant\"\n"
    "\n"
    "[file]\n"
    "id = 37\n"
    "name = \"most random number (according to polls)\"\n"
    "content = \"Hello, World!\"\n"
    "tags = \"epic drama\" \"classic\" \"super\\ncool!\"\n"
    "read_only = true\n"
    "executable = false\n";
  ini_parse(&SCRATCH, &ini_format, in);
  assert_cstr_eq(ini_fmt(&SCRATCH, &ini_format), expected_out);
}

// ==== internal ====

static struct Ini_Format ini_test_format(struct Ini_Test_Data* data)
{
  struct Ini_Format ini_format = {};

  {
    struct Ini_Format_Section section = {
      .name = "dir",
      .field_begin = ini_format.num_field_types,
      .field_end = ini_format.num_field_types,

      .section_data_capacity = ARRAY_LEN(data->dirs),
      .num_sections_read = &data->dir_count,
      .section_data = data->dirs,
      .section_entry_size = sizeof(struct Ini_Test_Directory),
    };
    ini_format.field_formats[section.field_end++] = (struct Ini_Format_Field){
      .name = "id",
      .type = INI_FIELD_TYPE_USIZE,
      .field_offset = offsetof(struct Ini_Test_Directory, id),
    };
    ini_format.field_formats[section.field_end++] = (struct Ini_Format_Field){
      .name = "name",
      .type = INI_FIELD_TYPE_CSTR,
      .field_offset = offsetof(struct Ini_Test_Directory, name),
    };
    ini_format.field_formats[section.field_end++] = (struct Ini_Format_Field){
      .name = "sub_ids",
      .type = INI_FIELD_TYPE_CSTR_ARRAY,
      .field_offset = offsetof(struct Ini_Test_Directory, sub_ids),
    };
    ini_format.section_formats[ini_format.num_sections++] = section;
  }
  {
    struct Ini_Format_Section section = {
      .name = "file",
      .field_begin = ini_format.num_field_types,
      .field_end = ini_format.num_field_types,

      .section_data_capacity = ARRAY_LEN(data->files),
      .num_sections_read = &data->file_count,
      .section_data = data->files,
      .section_entry_size = sizeof(struct Ini_Test_File),
    };
    ini_format.field_formats[section.field_end++] = (struct Ini_Format_Field){
      .name = "id",
      .type = INI_FIELD_TYPE_USIZE,
      .field_offset = offsetof(struct Ini_Test_File, id),
    };
    ini_format.field_formats[section.field_end++] = (struct Ini_Format_Field){
      .name = "name",
      .type = INI_FIELD_TYPE_CSTR,
      .field_offset = offsetof(struct Ini_Test_File, name),
    };
    ini_format.field_formats[section.field_end++] = (struct Ini_Format_Field){
      .name = "content",
      .type = INI_FIELD_TYPE_CSTR,
      .field_offset = offsetof(struct Ini_Test_File, content),
    };
    ini_format.field_formats[section.field_end++] = (struct Ini_Format_Field){
      .name = "tags",
      .type = INI_FIELD_TYPE_CSTR_ARRAY,
      .field_offset = offsetof(struct Ini_Test_File, tags),
    };
    ini_format.field_formats[section.field_end++] = (struct Ini_Format_Field){
      .name = "read_only",
      .type = INI_FIELD_TYPE_BOOL,
      .field_offset = offsetof(struct Ini_Test_File, read_only),
    };
    ini_format.field_formats[section.field_end++] = (struct Ini_Format_Field){
      .name = "executable",
      .type = INI_FIELD_TYPE_BOOL,
      .field_offset = offsetof(struct Ini_Test_File, executable),
    };
    ini_format.section_formats[ini_format.num_sections++] = section;
  }

  return ini_format;
}
