// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#include "proc.h"

#define READ_END 0
#define WRITE_END 1

struct Proc_Exec_Blocking_Result proc_exec_blocking(char* const args[], struct Proc_Exec_Blocking_Settings settings)
{
  int pipefd_stdout[2];
  int pipefd_stderr[2];
  if(settings.capture_stdout)
    LINUX_ASSERT_EQ(pipe(pipefd_stdout), 0);
  if(settings.capture_stderr)
    LINUX_ASSERT_EQ(pipe(pipefd_stderr), 0);

  const pid_t child_pid = fork();
  LINUX_ASSERT_NE(child_pid, -1);
  if(child_pid == 0)
  { // child process
    if(settings.capture_stdout)
    {
      close(pipefd_stdout[READ_END]);
      LINUX_ASSERT_NE(dup2(pipefd_stdout[WRITE_END], STDOUT_FILENO), -1);
    }
    if(settings.capture_stderr)
    {
      close(pipefd_stderr[READ_END]);
      LINUX_ASSERT_NE(dup2(pipefd_stderr[WRITE_END], STDERR_FILENO), -1);
    }

    execvp(args[0], args);
    UNREACHABLE();
  }

  if(settings.capture_stdout)
    LINUX_ASSERT_EQ(close(pipefd_stdout[WRITE_END]), 0);
  if(settings.capture_stderr)
    LINUX_ASSERT_EQ(close(pipefd_stderr[WRITE_END]), 0);

  int wstatus;
  LINUX_ASSERT_NE(waitpid(child_pid, &wstatus, 0), -1);

  struct Proc_Exec_Blocking_Result result = {
    .exit_code = WEXITSTATUS(wstatus),
    .exit_normal = WIFEXITED(wstatus),
  };
  result.success = result.exit_code==EXIT_SUCCESS && result.exit_normal;

  if(settings.capture_stdout)
  {
    result.captured_stdout = settings.region_stdout ? (char*)_linux_read_all_bytes_from_fd(pipefd_stdout[READ_END], settings.region_stdout).begin : NULL;
    LINUX_ASSERT_EQ(close(pipefd_stdout[READ_END]), 0);
  }
  
  if(settings.capture_stderr)
  {
    result.captured_stderr = settings.region_stderr ? (char*)_linux_read_all_bytes_from_fd(pipefd_stderr[READ_END], settings.region_stderr).begin : NULL;
    LINUX_ASSERT_EQ(close(pipefd_stderr[READ_END]), 0);
  }

  return result;

}

#undef READ_END
#undef WRITE_END

#undef pipe
