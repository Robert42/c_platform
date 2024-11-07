// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

// ==== ini file ====

struct Build_Ini_Action
{
  const char* name;

  const char** cmd;
  usize cmd_count;

  const char** trigger_fs_suffix;
  usize trigger_fs_suffix_count;

  const char** trigger_fs_path;
  usize trigger_fs_path_count;
};

#define MAX_NUM_ACTIONS 512
struct Build_Ini_Root
{
  struct Build_Ini_Action action[MAX_NUM_ACTIONS];
  usize action_count;
};

static struct Ini_Format build_ini_format(struct Build_Ini_Root* data)
{
  struct Ini_Format ini_format = {};

  {
    INI_FORMAT_SECTION_BEGIN(struct Build_Ini_Action, action, data->action, ARRAY_LEN(data->action), &data->action_count);
    INI_FORMAT_FIELD(name);
    INI_FORMAT_FIELD(cmd);
    INI_FORMAT_FIELD(trigger_fs_suffix);
    INI_FORMAT_FIELD(trigger_fs_path);
    INI_FORMAT_SECTION_END();
  }

  return ini_format;
}

