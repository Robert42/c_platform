// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

// usefulf commands whlie working on codegeneration:
// - `git restore [PATH]`

#include "c_script.h"

const char* const BANNER =
"// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.\n"
"// >> AUTOGENERATED!!! << NO NOT MODIFY! >> Modifications will be overwritten!!\n"
;

#include "platform/codegen.c"

int main(int argc, char** argv)
{
  c_script_init();

  platform_codegen();

  printf("%s==== DONE ====%s\n", TERM_GREEN_BOLD, TERM_NORMAL);

  return EXIT_SUCCESS;
}
