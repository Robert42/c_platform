// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "proc.h"

struct Proc_Exec_Blocking_Result proc_exec_blocking(char* const args[], struct Proc_Exec_Blocking_Settings settings)
{
  int pipefd_stdout[2];
  if(settings.capture_stdout)
    LINUX_ASSERT_EQ(pipe(pipefd_stdout), 0);
  // TODO: pipe for stderr

  const pid_t child_pid = fork();
  if(child_pid == 0) // Is this the child process?
  {
    execvp(args[0], args);
  }

  if(settings.capture_stdout)
  {
    LINUX_ASSERT_EQ(close(pipefd_stdout[0]), 0);
    LINUX_ASSERT_EQ(close(pipefd_stdout[1]), 0);
  }

  return (struct Proc_Exec_Blocking_Result){};
}

