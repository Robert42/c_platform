// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "../../c_script.h"

int main(int argc, char** argv)
{
  c_script_init();

  assert_int_gt(argc, 0);
  if(argc != 2)
    printf("USAGE: %s <FILE>\n", argv[0]);
}

