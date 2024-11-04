// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "ini_format.h"

enum Project_Action_Variant
{
  ACTION_NONE,
  ACTION_CC,
};

struct Project_Action
{
  const char* name;

  enum Project_Action_Variant variant;
  union
  {
    struct C_Compiler_Config cc;
  };

  const char** trigger_fs_suffix;
  usize trigger_fs_suffix_count;

  const char** trigger_fs_path;
  usize trigger_fs_path_count;
};

struct Project
{
  struct Project_Action action[MAX_NUM_ACTIONS];
  usize action_count;
};

