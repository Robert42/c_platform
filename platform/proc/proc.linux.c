// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "proc.h"

#define READ_END 0
#define WRITE_END 1

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
      close(pipefd_stdout[READ_END]);
      LINUX_ASSERT_NE(dup2(pipefd_stdout[WRITE_END], STDOUT_FILENO), -1);
    }

    execvp(args[0], args);
    UNREACHABLE();
  }

  if(settings.capture_stdout)
    LINUX_ASSERT_EQ(close(pipefd_stdout[WRITE_END]), 0);
  
  LINUX_ASSERT_NE(waitpid(child_pid, NULL, 0), -1);

  struct Proc_Exec_Blocking_Result result = {};
  

  if(settings.capture_stdout)
  {
    Mem_Region* region = settings.region_stdout;
    const size_t bytes_available = region->end-region->begin;
    ssize_t bytes_read = read(pipefd_stdout[READ_END], region->begin, bytes_available);
    LINUX_ASSERT_NE(bytes_read, -1);

    result.captured_stdout = region->begin;
    region->begin += bytes_read;

    // Add nullterminator
    assert_ptr_lt(region->begin, region->end); // No more space for the nullterminator
    *(uint8_t*)region->begin = 0;
    region->begin++;
    // TODO: typedef int types
  
    LINUX_ASSERT_EQ(close(pipefd_stdout[READ_END]), 0);
  }

  return result;

}

#undef READ_END
#undef WRITE_END

