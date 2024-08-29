// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

enum C_Static_Analyzer
{
  CSA_FRAMA_C_EVA,
};
#define C_STATIC_ANALYZER_COUNT 1

bool c_static_analysis(enum C_Static_Analyzer csa, Path c_file);

extern const char* C_STATIC_ANALYZER_NAMES[C_STATIC_ANALYZER_COUNT];
enum C_Static_Analyzer c_static_analyzer_for_name(const char* name);

