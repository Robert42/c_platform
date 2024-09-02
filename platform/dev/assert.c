// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
// >> AUTOGENERATED!!! << NO NOT MODIFY! >> Modifications will be overwritten!!
#ifndef __FRAMAC__

// ==== usize ====
void __assert_usize_eq__(usize x, usize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x == y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%zu", x), str_fmt(&SCRATCH, "%zu", y), file, line);
}
void __assert_usize_ne__(usize x, usize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x != y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%zu", x), str_fmt(&SCRATCH, "%zu", y), file, line);
}
void __assert_usize_lt__(usize x, usize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x < y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%zu", x), str_fmt(&SCRATCH, "%zu", y), file, line);
}
void __assert_usize_lte__(usize x, usize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%zu", x), str_fmt(&SCRATCH, "%zu", y), file, line);
}
void __assert_usize_gt__(usize x, usize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x > y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%zu", x), str_fmt(&SCRATCH, "%zu", y), file, line);
}
void __assert_usize_gte__(usize x, usize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x >= y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%zu", x), str_fmt(&SCRATCH, "%zu", y), file, line);
}
void __assert_usize_lte_lte__(usize x, usize y, usize z, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y && y <= z))
    return;
  else
  __ter_assert_failed__(condition, str_fmt(&SCRATCH, "%zu", x), str_fmt(&SCRATCH, "%zu", y), str_fmt(&SCRATCH, "%zu", z), file, line);
}
void __assert_usize_lte_lt__(usize x, usize y, usize z, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y && y < z))
    return;
  else
  __ter_assert_failed__(condition, str_fmt(&SCRATCH, "%zu", x), str_fmt(&SCRATCH, "%zu", y), str_fmt(&SCRATCH, "%zu", z), file, line);
}

// ==== ssize ====
void __assert_ssize_eq__(ssize x, ssize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x == y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%zs", x), str_fmt(&SCRATCH, "%zs", y), file, line);
}
void __assert_ssize_ne__(ssize x, ssize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x != y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%zs", x), str_fmt(&SCRATCH, "%zs", y), file, line);
}
void __assert_ssize_lt__(ssize x, ssize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x < y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%zs", x), str_fmt(&SCRATCH, "%zs", y), file, line);
}
void __assert_ssize_lte__(ssize x, ssize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%zs", x), str_fmt(&SCRATCH, "%zs", y), file, line);
}
void __assert_ssize_gt__(ssize x, ssize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x > y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%zs", x), str_fmt(&SCRATCH, "%zs", y), file, line);
}
void __assert_ssize_gte__(ssize x, ssize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x >= y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%zs", x), str_fmt(&SCRATCH, "%zs", y), file, line);
}
void __assert_ssize_lte_lte__(ssize x, ssize y, ssize z, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y && y <= z))
    return;
  else
  __ter_assert_failed__(condition, str_fmt(&SCRATCH, "%zs", x), str_fmt(&SCRATCH, "%zs", y), str_fmt(&SCRATCH, "%zs", z), file, line);
}
void __assert_ssize_lte_lt__(ssize x, ssize y, ssize z, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y && y < z))
    return;
  else
  __ter_assert_failed__(condition, str_fmt(&SCRATCH, "%zs", x), str_fmt(&SCRATCH, "%zs", y), str_fmt(&SCRATCH, "%zs", z), file, line);
}

// ==== int ====
void __assert_int_eq__(int x, int y, const char* condition, const char* file, int line)
{
  if(LIKELY(x == y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%i", x), str_fmt(&SCRATCH, "%i", y), file, line);
}
void __assert_int_ne__(int x, int y, const char* condition, const char* file, int line)
{
  if(LIKELY(x != y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%i", x), str_fmt(&SCRATCH, "%i", y), file, line);
}
void __assert_int_lt__(int x, int y, const char* condition, const char* file, int line)
{
  if(LIKELY(x < y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%i", x), str_fmt(&SCRATCH, "%i", y), file, line);
}
void __assert_int_lte__(int x, int y, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%i", x), str_fmt(&SCRATCH, "%i", y), file, line);
}
void __assert_int_gt__(int x, int y, const char* condition, const char* file, int line)
{
  if(LIKELY(x > y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%i", x), str_fmt(&SCRATCH, "%i", y), file, line);
}
void __assert_int_gte__(int x, int y, const char* condition, const char* file, int line)
{
  if(LIKELY(x >= y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%i", x), str_fmt(&SCRATCH, "%i", y), file, line);
}

// ==== ptr ====
void __assert_ptr_eq__(const void* x, const void* y, const char* condition, const char* file, int line)
{
  if(LIKELY(x == y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%p", x), str_fmt(&SCRATCH, "%p", y), file, line);
}
void __assert_ptr_ne__(const void* x, const void* y, const char* condition, const char* file, int line)
{
  if(LIKELY(x != y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%p", x), str_fmt(&SCRATCH, "%p", y), file, line);
}
void __assert_ptr_lt__(const void* x, const void* y, const char* condition, const char* file, int line)
{
  if(LIKELY(x < y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%p", x), str_fmt(&SCRATCH, "%p", y), file, line);
}
void __assert_ptr_lte__(const void* x, const void* y, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%p", x), str_fmt(&SCRATCH, "%p", y), file, line);
}
void __assert_ptr_gt__(const void* x, const void* y, const char* condition, const char* file, int line)
{
  if(LIKELY(x > y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%p", x), str_fmt(&SCRATCH, "%p", y), file, line);
}
void __assert_ptr_gte__(const void* x, const void* y, const char* condition, const char* file, int line)
{
  if(LIKELY(x >= y))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(&SCRATCH, "%p", x), str_fmt(&SCRATCH, "%p", y), file, line);
}
void __assert_ptr_lte_lte__(const void* x, const void* y, const void* z, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y && y <= z))
    return;
  else
  __ter_assert_failed__(condition, str_fmt(&SCRATCH, "%p", x), str_fmt(&SCRATCH, "%p", y), str_fmt(&SCRATCH, "%p", z), file, line);
}
void __assert_ptr_lte_lt__(const void* x, const void* y, const void* z, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y && y < z))
    return;
  else
  __ter_assert_failed__(condition, str_fmt(&SCRATCH, "%p", x), str_fmt(&SCRATCH, "%p", y), str_fmt(&SCRATCH, "%p", z), file, line);
}

// ==== cstr_eq ====
void __assert_cstr_eq__(const char* x, const char* y)
{
  if(LIKELY((strcmp(x,y) == 0)))
    return;
  else
  __assert_failed__();
}

// ==== bool_eq ====
void __assert_bool_eq__(bool x, bool y)
{
  if(LIKELY(x == y))
    return;
  else
  __assert_failed__();
}

#endif // __FRAMAC__
