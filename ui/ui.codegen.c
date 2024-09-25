// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.

#include "ui.h"

#define CODEGEN_WAYLAND __linux__ && 0

#if CODEGEN_WAYLAND
#include "backend/wayland/wayland_protocol.codegen.c"
#endif

void ui_codegen()
{
#if CODEGEN_WAYLAND
  wayland_protocol_codegen();
#endif
}
