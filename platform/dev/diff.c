// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

void print_cstr_diff(const char* x, const char* y)
{
#if __linux__
  // TODO: function to create a temp dir?
  Path x_path = path_from_cstr("/tmp/diff_x");
  Path y_path = path_from_cstr("/tmp/diff_y");
  file_text_create_from_cstr(x_path, x);
  file_text_create_from_cstr(y_path, y);
  char* const args[] = {
    "sdiff",
    x_path.cstr,
    y_path.cstr,
    NULL,
  };
  struct Proc_Exec_Blocking_Result result = proc_exec_blocking(args, (struct Proc_Exec_Blocking_Settings){0});
  assert(result.exit_normal);
#endif
}

void print_str_diff(str x, str y)
{
  TODO();
}
