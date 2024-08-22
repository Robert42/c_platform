// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "proc.h"

struct Proc_Exec_Blocking_Result proc_exec_blocking(char* const args[], struct Proc_Exec_Blocking_Settings settings)
{
  int pipefd_stdout[2];
  if(settings.capture_stdout)
    LINUX_ASSERT_EQ(pipe(pipefd_stdout), 0);
  // TODO: pipe for stderr

  const pid_t child_pid = fork();
  LINUX_ASSERT_NE(child_pid, -1);
  if(child_pid == 0)
  { // child process
    if(settings.capture_stdout)
    {
      LINUX_ASSERT_NE(dup2(pipefd_stdout[1], STDOUT_FILENO), -1);
    }

    execvp(args[0], args);
    UNREACHABLE();
  }
  
  LINUX_ASSERT_NE(waitpid(child_pid, NULL, 0), -1);

  struct Proc_Exec_Blocking_Result result = {};

  if(settings.capture_stdout)
  {
    Mem_Region* region = settings.region_stdout;
    const size_t bytes_available = region->end-region->begin;
    ssize_t bytes_read = read(pipefd_stdout[0], region->begin, bytes_available);
    LINUX_ASSERT_NE(bytes_read, -1);

    if(bytes_read == bytes_available)
    {
      // TODO: check if the buffer was large enough
    }

    result.captured_stdout = region->begin;
    // TODO:
    // region->begin += bytes_read;
  
    LINUX_ASSERT_EQ(close(pipefd_stdout[0]), 0);
    LINUX_ASSERT_EQ(close(pipefd_stdout[1]), 0);
  }

  return result;
}

