// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct Proc_Exec_Blocking_Settings
{
  bool capture_stdout : 1;
  bool capture_stderr : 1;
  Mem_Region* region_stdout;
  Mem_Region* region_stderr;
};

struct Proc_Exec_Blocking_Result
{
  char* captured_stdout;
  char* captured_stderr;
  int exit_code;
};

struct Proc_Exec_Blocking_Result proc_exec_blocking(char* const args[], struct Proc_Exec_Blocking_Settings settings);

