// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "ui.h"

#if __linux__
#include "backend/wayland/wayland_protocol.codegen.c"
#endif

void ui_codegen()
{
#if __linux__
  wayland_protocol_codegen();
#endif
}
