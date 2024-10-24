// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "../../c_script.h"

struct Unit_Test
{
  const char* src;
};

struct Build_System_Data
{
  struct Unit_Test unit_test[1024];
  usize unit_test_count;
};

static struct Ini_Format build_system_format(struct Build_System_Data* data);

int main(int argc, char** argv)
{
  c_script_init();

  Path config_file;
  switch(argc)
  {
  case 0:
  case 1:
    config_file = path_from_cstr("build.ini");
    break;
  case 2:
    config_file = path_from_cstr(argv[1]);
    break;
  default:
    printf("USAGE: %s [FILE]\n", argv[0]);
    return 0;
  }

  struct Build_System_Data data = {};
  struct Ini_Format ini_format = build_system_format(&data);
  {
    const Mem_Region _prev = STACK;
    const char* text = file_text_read_to_cstr(config_file, &STACK);
    ini_parse(&SCRATCH, &ini_format, text);
    STACK = _prev;
  }
  printf("TODO:\n%s\n", ini_fmt(&SCRATCH, &ini_format));
}

static struct Ini_Format build_system_format(struct Build_System_Data* data)
{
  struct Ini_Format ini_format = {};

  {
    INI_FORMAT_SECTION_BEGIN(struct Unit_Test, unit_test, data->unit_test, ARRAY_LEN(data->unit_test), &data->unit_test_count);
    INI_FORMAT_FIELD(src);
    INI_FORMAT_SECTION_END();
  }

  return ini_format;
}
