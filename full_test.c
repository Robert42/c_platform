// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "platform/platform.c"
#include "utils/utils.c"

#include "platform/test.c"
#include "utils/test.c"

#include "c_compiler/c_static_analysis.c"

static u8 _SCRATCH_BUFFER_1[1024*1024] = {0};
Mem_Region SCRATCH = {0};

#define TERM_HEADER TERM_NORMAL

void print_running(const char* name)
{
  printf("%s running...", name);
  fflush(stdout);
}
void print_result(const char* style_name, const char* name, const char* style_result, const char* result)
{
  printf("%s%s%s%s %s%s\n", TERM_CLEAR_LINE, style_name, name, style_result, result, TERM_NORMAL);
  fflush(stdout);
}
void handle_result(const char* name, bool ok);

int main(int argc, const char** argv)
{
  platform_init();
  
  const Path full_test_file = path_from_cstr(__FILE__);

  SCRATCH = MEM_REGION_FROM_ARRAY(_SCRATCH_BUFFER_1);

  printf(TERM_CLEAR);
  fflush(stdout);


  printf("%s==== static analysis ====%s\n", TERM_HEADER, TERM_NORMAL);

  for(u32 i=0; i<C_STATIC_ANALYZER_COUNT; ++i)
  {
    const char* name = C_STATIC_ANALYZER_NAMES[i];
    print_running(name);
    const bool ok = c_static_analysis(i, full_test_file);
    handle_result(name, ok);
  }

  printf("%s==== run tests ====%s\n", TERM_HEADER, TERM_NORMAL);
  platform_test();
  utils_test();

  printf("%s==== DONE ====%s\n", TERM_GREEN_BOLD, TERM_NORMAL);

  return EXIT_SUCCESS;
}

void handle_result(const char* name, bool ok)
{
  if(ok)
    print_result(TERM_GREEN, name, TERM_GREEN_BOLD, "OK");
  else
  {
    print_result(TERM_RED, name, TERM_RED_BOLD, "FAILED");
    exit(EXIT_FAILURE);
  }
}
