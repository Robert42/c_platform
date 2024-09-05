// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
#pragma once

#ifndef I_HAVE_MANUALLY_ADDED_THE_SPEC_TO_THE_FRAMA_C_STDLIB

/*@
    terminates false;
    ensures result_nullterminated: 0 <= \result < n ==> s[\result]==0;
    ensures truncated_nullterminated: 0 < n <= \result ==> s[n-1]==0;
    exits false;
*/
int vsnprintf(char* s, usize n, const char* format, va_list args);

#endif
