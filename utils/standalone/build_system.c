// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "../../c_script.h"
#include "libtcc.h"

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

  printf("TODO: parse <%s>\n", config_file.cstr);
}

