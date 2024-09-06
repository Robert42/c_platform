// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

struct _platform_io_Bytes;
typedef struct _platform_io_Bytes Bytes;

struct _platform_io_Bytes
{
  u8* begin;
  u8* end;
};

