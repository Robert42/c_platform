// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct Proc_Exec_Settings
{
  bool block : 1; // wait for the process to finish
  bool capture_stdout : 1;
  bool capture_stderr : 1;
  Mem_Region* region_stdout;
  Mem_Region* region_stderr;
};

struct Proc_Exec_Result
{
  int result;
  const char* captured_stdout;
  const char* captured_stderr;
};

struct Proc_Exec_Result proc_exec(const char* command, struct Proc_Exec_Settings settings);

