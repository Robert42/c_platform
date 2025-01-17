// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "ui.h"
#include "backend/wayland/wayland_connection.c"

enum Desktop_Session_Type DESKTOP_SESSION_TYPE = DST_UNKNOWN;

void ui_init()
{
#ifdef __linux__
  const char* session_type = getenv_or_panic("XDG_SESSION_TYPE");
  if(strcmp(session_type, "wayland") == 0)
    DESKTOP_SESSION_TYPE = DST_WAYLAND;
  else if(strcmp(session_type, "x11") == 0)
    DESKTOP_SESSION_TYPE = DST_X11;
  else
    PANIC("Unknown desktop session type `%s`\n", session_type);
#endif
}
