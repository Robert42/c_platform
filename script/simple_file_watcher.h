// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

typedef bool Fn_File_Filter(const char* filepath);

struct Simple_File_Watcher
{
  Fn_File_Filter *filter;

#ifdef __linux__
  int fd;
#endif
};

struct Simple_File_Watcher simple_file_watcher_init(const char* root_path, Fn_File_Filter *filter);
bool simple_file_watcher_wait_for_change(struct Simple_File_Watcher* watcher);

