// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "ini.h"

struct Ini_Test_Directory
{
  usize id;

  const char* name;

  const char** sub_ids;
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
  struct Ini_Test_Data test_data = {};

  struct Ini_Format ini_format = ini_test_format(&test_data);

  const char* in =
    "[dir]\n"
    "id = 42\n"
    "name = \"answer of life\"\n"
    "sub_ids = 37 137"
    "\n"
    "[file]\n"
    "id = 37\n"
    "name = \"most random number (according to polls)\"\n"
    "content = \"Hello, World!\"\n"
    "tags = \"epic drama\" classic \"super\\ncool!\"\n"
    "read_only = true\n"
    "\n"
    "[dir]\n"
    "id = 137\n"
    "name = \"the fienstructure constant\"\n"
    ;
  const char* expected_out =
    "[dir]\n"
    "id = 42\n"
    "name = \"answer of life\"\n"
    "sub_ids = \"37\" \"137\"\n"
    "\n"
    "[dir]\n"
    "id = 137\n"
    "name = \"the fienstructure constant\"\n"
    "sub_ids =\n"
    "\n"
    "[file]\n"
    "id = 37\n"
    "name = \"most random number (according to polls)\"\n"
    "content = \"Hello, World!\"\n"
    "tags = \"epic drama\" \"classic\" \"super\\ncool!\"\n"
    "read_only = true\n"
    "executable = false\n";
  ini_parse(&SCRATCH, &ini_format, in);
  const char* out = ini_fmt(&SCRATCH, &ini_format);
  assert_cstr_eq(out, expected_out);
}

// ==== internal ====

static struct Ini_Format ini_test_format(struct Ini_Test_Data* data)
{
  struct Ini_Format ini_format = {};

  {
    INI_FORMAT_SECTION_BEGIN(struct Ini_Test_Directory, dir, data->dirs, ARRAY_LEN(data->dirs), &data->dir_count);
    INI_FORMAT_FIELD(id);
    INI_FORMAT_FIELD(name);
    INI_FORMAT_FIELD(sub_ids);
    INI_FORMAT_SECTION_END();
  }
  {
    INI_FORMAT_SECTION_BEGIN(struct Ini_Test_File, file, data->files, ARRAY_LEN(data->files), &data->file_count);
    INI_FORMAT_FIELD(id);
    INI_FORMAT_FIELD(name);
    INI_FORMAT_FIELD(content);
    INI_FORMAT_FIELD(tags);
    INI_FORMAT_FIELD(read_only);
    INI_FORMAT_FIELD(executable);
    INI_FORMAT_SECTION_END();
  }

  return ini_format;
}
