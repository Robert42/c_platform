// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

Path wayland_protocol_dir();

void wayland_protocol_codegen()
{
  printf("wayland_protocol_dir(): `%s`\n", wayland_protocol_dir().cstr);
}

Path wayland_protocol_dir()
{
  Path result_path = {0};
  Mem_Region region = _mem_region_from(result_path.cstr, PATH_LEN_MAX+1);

  char* const args[] = {"pkg-config", "--variable=pkgdatadir", "wayland-protocols", NULL};
  const struct Proc_Exec_Blocking_Settings settings = {
    .capture_stdout = true,
    .region_stdout = &region,
  };
  struct Proc_Exec_Blocking_Result result = proc_exec_blocking(args, settings);
  assert(result.success);

  cstr_trim_right(result_path.cstr);
  result_path.len = strlen(result_path.cstr);

  return result_path;
}
