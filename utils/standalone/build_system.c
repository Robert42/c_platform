// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "../../c_script.h"
#include "libtcc.h"

// Custom implementation of the bash command `time`
// ```
// cc -O2 ./utils/standalone/build_system.c `pkg-config --cflags --libs libtcc` -o ./utils/standalone/__build_c__
// ```


int main(int argc, char** argv)
{
  c_script_init();

  assert_int_gt(argc, 0);
  if(argc != 2)
  {
    printf("USAGE: %s <FILE>\n", argv[0]);
    return 0;
  }

  Path program = path_from_cstr(argv[0]);


  {
    char* const args[] = {
#ifdef __unix__
      "which",
#else
#error untested
      "where",
#endif
      argv[0],
      NULL,
    };
    struct Proc_Exec_Blocking_Result result = proc_exec_blocking(args, (struct Proc_Exec_Blocking_Settings){.capture_stdout=true, .region_stdout=&SCRATCH});
    assert_bool_eq(result.success, true);
    cstr_trim_right(result.captured_stdout);
    program = path_from_cstr(result.captured_stdout);
  }
  program = path_realpath(program);

  TCCState* tcc = tcc_new();

  const Path include_path = path_join(path_parent(program), path_from_cstr("include"));
  tcc_add_include_path(tcc, include_path.cstr);
  tcc_add_file(tcc, argv[1]);

  

  tcc_delete(tcc);
}

