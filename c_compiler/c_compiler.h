// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

enum C_Compiler
{
  CC_TCC,
  CC_GCC,
  CC_CLANG,
};
#define CC_COUNT 3

enum Static_Analysis
{
  STATIC_ANALYSIS_NONE,
  STATIC_ANALYSIS_NATIVE,
  STATIC_ANALYSIS_FRAMA_C_WP,
  STATIC_ANALYSIS_FRAMA_C_EVA,
};

enum C_Version
{
  C_VERSION_1989,
  C_VERSION_1999,
  C_VERSION_2011,
  C_VERSION_GNU_1989,
  C_VERSION_GNU_1999,
  C_VERSION_GNU_2011,
};

struct C_Compiler_Config
{
  enum C_Compiler cc : 8; // `gcc`, `clang`, `tcc`, ...
  enum C_Version c_version : 4; // `-std=c89`, `-std=c99`, `-std=c11`
  enum Static_Analysis static_analysis : 4;
  bool debug : 1; // `-g`
  bool disable_vla : 1; // `-Werror=vla`
  bool skip_warning_flags : 1; // used by tests to reduce duplicate testcases
  bool sanitize_memory : 1;
  bool gen_parent_dir : 1;

  bool capture_run_stdout : 1; // ignored if `run_args` is NULL
  bool capture_run_stderr : 1; // ignored if `run_args` is NULL
  Path capture_run_stdout_filepath; // `> output_filepath`
  Path capture_run_stderr_filepath; // `2> output_filepath`

  Path c_file; // ignored with `run_args` is NULL
  Path output_file; // `-o file_out`

  Path* include_dir[32]; // `-Ia/b/c`
  usize include_dir_count;

  // - If null: `-o file_out`
  // - If not null: List of run_args_count arguments. `-o file_out && file_out run_args[0] run_args[1] ... run_args[run_args_count-1]`
  const char** run_args;
  usize run_args_count;
};

enum CC_Single_Status
{
  STATUS_IGNORED = 0,
  STATUS_PENDING,
  STATUS_FAILED,
  STATUS_SUCCEEDED,
};

struct CC_Status
{
  enum CC_Single_Status compile, static_analysis, run;
};
bool cc_status_is_success(struct CC_Status s);
const char* cc_status_attempted_name(struct CC_Status s);

struct CC_Status cc_run(struct C_Compiler_Config cfg);
void cc_command_fmt(Fmt* f, struct C_Compiler_Config cfg);
void cc_command_print(struct C_Compiler_Config cfg);

bool cc_compile_and_run(enum C_Compiler cc, Path c_file, Path output_file);
enum C_Compiler cc_compiler_for_name(const char* name); // will call errx, if the name is an unknown compiler
const char* cc_compiler_name(enum C_Compiler cc);
bool cc_is_compiler_name(const char* name);

enum C_Version cc_version_for_name(const char* name); // will call errx, if the name is an unknown compiler

enum C_Compiler cc_fastest_available();
enum C_Compiler cc_best_optimizer_available();
bool cc_compiler_is_available(enum C_Compiler cc);

void cc_init();

