// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

typedef bool Fn_File_Filter(const char* filepath);

// TODO: this probably confuses tcc's #pragma once system
#include "../utils/collections/set/setintcddo.c"

struct Simple_File_Watcher
{
  Fn_File_Filter *filter; // Determines for a given filename, whether a file is relevant

#ifdef __linux__
  // Use two inotify instances: one for directories, one for the relevant files
  // only.
  //
  // When the directory structure changes, I can recreate the watchers for it
  // while being able to use the other inotify instance (same files get the
  // same watch descriptor) to check, whether any relevant files were added
  // or removed.
  int dirs_fd; // inode fd for directory changes
  int file_fd; // inode fd for directory changes
  // TODO: decide, whether go back to one inotify file descriptor again?
  char* root_path;

  // TODO: cache the blake3 hashsum of the last modified file? If an modify event is recevied for the same file, check, whether it realy changed?
  struct Set_Int_Change_Detection_Dismissing_Old* watched_files;
#endif
};

struct Simple_File_Watcher simple_file_watcher_init(const char* root_path, Fn_File_Filter *filter);
void simple_file_watcher_deinit(struct Simple_File_Watcher* watcher);
bool simple_file_watcher_wait_for_change(struct Simple_File_Watcher* watcher);

