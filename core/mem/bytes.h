// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct _platform_io_Bytes_Mut;
typedef struct _platform_io_Bytes_Mut Bytes_Mut;

struct _platform_io_Bytes_Mut
{
  u8* begin;
  u8* end;
};

