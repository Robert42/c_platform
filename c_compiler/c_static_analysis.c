// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "c_static_analysis.h"

const char* C_STATIC_ANALYZER_NAMES[C_STATIC_ANALYZER_COUNT] = {
  [CSA_FRAMA_C_EVA] = "frama_c.eva",
};

bool c_static_analysis(enum C_Static_Analyzer csa, Path c_file)
{
  struct Proc_Exec_Blocking_Settings capture_everything = {
    .capture_stdout = true,
    .capture_stderr = true,
    .region_stdout = &SCRATCH,
    .region_stderr = &SCRATCH,
  };

  switch(csa)
  {
  case CSA_FRAMA_C_EVA:
  {
    char* const args_compile[] = {"frama-c", "-eva-precision", "3", "-eva", c_file.cstr, NULL};
    struct Proc_Exec_Blocking_Result result = proc_exec_blocking(args_compile, capture_everything);
    if(result.exit_code != EXIT_SUCCESS)
      return false;
    return !strstr(result.captured_stdout, "Some errors and warnings have been raised during the analysis");
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
