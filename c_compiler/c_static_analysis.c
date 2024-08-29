// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "c_static_analysis.h"

const char* C_STATIC_ANALYZER_NAMES[C_STATIC_ANALYZER_COUNT] = {
  [CSA_FRAMA_C_EVA] = "frama_c.eva",
};

void c_static_analysis(enum C_Static_Analyzer csa, Path c_file)
{
  switch(csa)
  {
  case CSA_FRAMA_C_EVA:
  {
    char* const args_compile[] = {"frama-c", "-eva-precision", "3", "-eva", c_file.cstr, NULL};
    proc_exec_blocking(args_compile, (struct Proc_Exec_Blocking_Settings){0});
    break;
  }
  }
}

enum C_Static_Analyzer c_static_analyzer_for_name(const char* name)
{
  for(u32 i=0; i<C_STATIC_ANALYZER_COUNT; ++i)
    if(strcmp(C_STATIC_ANALYZER_NAMES[i], name) == 0)
      return i;

  errx(EXIT_FAILURE, "Unknown static analyzer `%s`", name);
}
