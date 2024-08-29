// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

void timer_init();

extern u64 timer_freq;
u64 timer_now();
const char* time_format_short_duration(u64 time, Mem_Region* region);

const char* time_format_date_time_now(Mem_Region* region);
