// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#ifdef __linux__
#include <signal.h>

volatile bool exit_requested = false;
static void _handle_sigint_for_graceful_exit(int sig){exit_requested=true;}
void register_graceful_exit_via_sigint()
{
  struct sigaction action = {
    .sa_handler = _handle_sigint_for_graceful_exit,
  };
  sigaction(SIGINT, &action, NULL);
}
#endif
