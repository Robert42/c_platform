// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
// >> AUTOGENERATED!!! << NO NOT MODIFY! >> Modifications will be overwritten!!
#ifndef __FRAMAC__

// ==== usize ====
void __assert_usize_eq__(usize x, usize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x == y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zu", x), cstr_fmt(&PANIC_REGION, "%zu", y), file, line);
}
void __assert_usize_ne__(usize x, usize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x != y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zu", x), cstr_fmt(&PANIC_REGION, "%zu", y), file, line);
}
void __assert_usize_lt__(usize x, usize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x < y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zu", x), cstr_fmt(&PANIC_REGION, "%zu", y), file, line);
}
void __assert_usize_lte__(usize x, usize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zu", x), cstr_fmt(&PANIC_REGION, "%zu", y), file, line);
}
void __assert_usize_gt__(usize x, usize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x > y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zu", x), cstr_fmt(&PANIC_REGION, "%zu", y), file, line);
}
void __assert_usize_gte__(usize x, usize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x >= y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zu", x), cstr_fmt(&PANIC_REGION, "%zu", y), file, line);
}
void __assert_usize_lte_lte__(usize x, usize y, usize z, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y && y <= z))
    return;
  else
  __ter_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zu", x), cstr_fmt(&PANIC_REGION, "%zu", y), cstr_fmt(&PANIC_REGION, "%zu", z), file, line);
}
void __assert_usize_lte_lt__(usize x, usize y, usize z, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y && y < z))
    return;
  else
  __ter_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zu", x), cstr_fmt(&PANIC_REGION, "%zu", y), cstr_fmt(&PANIC_REGION, "%zu", z), file, line);
}

// ==== ssize ====
void __assert_ssize_eq__(ssize x, ssize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x == y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zs", x), cstr_fmt(&PANIC_REGION, "%zs", y), file, line);
}
void __assert_ssize_ne__(ssize x, ssize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x != y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zs", x), cstr_fmt(&PANIC_REGION, "%zs", y), file, line);
}
void __assert_ssize_lt__(ssize x, ssize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x < y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zs", x), cstr_fmt(&PANIC_REGION, "%zs", y), file, line);
}
void __assert_ssize_lte__(ssize x, ssize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zs", x), cstr_fmt(&PANIC_REGION, "%zs", y), file, line);
}
void __assert_ssize_gt__(ssize x, ssize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x > y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zs", x), cstr_fmt(&PANIC_REGION, "%zs", y), file, line);
}
void __assert_ssize_gte__(ssize x, ssize y, const char* condition, const char* file, int line)
{
  if(LIKELY(x >= y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zs", x), cstr_fmt(&PANIC_REGION, "%zs", y), file, line);
}
void __assert_ssize_lte_lte__(ssize x, ssize y, ssize z, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y && y <= z))
    return;
  else
  __ter_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zs", x), cstr_fmt(&PANIC_REGION, "%zs", y), cstr_fmt(&PANIC_REGION, "%zs", z), file, line);
}
void __assert_ssize_lte_lt__(ssize x, ssize y, ssize z, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y && y < z))
    return;
  else
  __ter_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%zs", x), cstr_fmt(&PANIC_REGION, "%zs", y), cstr_fmt(&PANIC_REGION, "%zs", z), file, line);
}

// ==== int ====
void __assert_int_eq__(int x, int y, const char* condition, const char* file, int line)
{
  if(LIKELY(x == y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%i", x), cstr_fmt(&PANIC_REGION, "%i", y), file, line);
}
void __assert_int_ne__(int x, int y, const char* condition, const char* file, int line)
{
  if(LIKELY(x != y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%i", x), cstr_fmt(&PANIC_REGION, "%i", y), file, line);
}
void __assert_int_lt__(int x, int y, const char* condition, const char* file, int line)
{
  if(LIKELY(x < y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%i", x), cstr_fmt(&PANIC_REGION, "%i", y), file, line);
}
void __assert_int_lte__(int x, int y, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%i", x), cstr_fmt(&PANIC_REGION, "%i", y), file, line);
}
void __assert_int_gt__(int x, int y, const char* condition, const char* file, int line)
{
  if(LIKELY(x > y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%i", x), cstr_fmt(&PANIC_REGION, "%i", y), file, line);
}
void __assert_int_gte__(int x, int y, const char* condition, const char* file, int line)
{
  if(LIKELY(x >= y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%i", x), cstr_fmt(&PANIC_REGION, "%i", y), file, line);
}

// ==== ptr ====
void __assert_ptr_eq__(const void* x, const void* y, const char* condition, const char* file, int line)
{
  if(LIKELY(x == y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%p", x), cstr_fmt(&PANIC_REGION, "%p", y), file, line);
}
void __assert_ptr_ne__(const void* x, const void* y, const char* condition, const char* file, int line)
{
  if(LIKELY(x != y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%p", x), cstr_fmt(&PANIC_REGION, "%p", y), file, line);
}
void __assert_ptr_lt__(const void* x, const void* y, const char* condition, const char* file, int line)
{
  if(LIKELY(x < y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%p", x), cstr_fmt(&PANIC_REGION, "%p", y), file, line);
}
void __assert_ptr_lte__(const void* x, const void* y, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%p", x), cstr_fmt(&PANIC_REGION, "%p", y), file, line);
}
void __assert_ptr_gt__(const void* x, const void* y, const char* condition, const char* file, int line)
{
  if(LIKELY(x > y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%p", x), cstr_fmt(&PANIC_REGION, "%p", y), file, line);
}
void __assert_ptr_gte__(const void* x, const void* y, const char* condition, const char* file, int line)
{
  if(LIKELY(x >= y))
    return;
  else
  __bin_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%p", x), cstr_fmt(&PANIC_REGION, "%p", y), file, line);
}
void __assert_ptr_lte_lte__(const void* x, const void* y, const void* z, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y && y <= z))
    return;
  else
  __ter_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%p", x), cstr_fmt(&PANIC_REGION, "%p", y), cstr_fmt(&PANIC_REGION, "%p", z), file, line);
}
void __assert_ptr_lte_lt__(const void* x, const void* y, const void* z, const char* condition, const char* file, int line)
{
  if(LIKELY(x <= y && y < z))
    return;
  else
  __ter_assert_failed__(condition, cstr_fmt(&PANIC_REGION, "%p", x), cstr_fmt(&PANIC_REGION, "%p", y), cstr_fmt(&PANIC_REGION, "%p", z), file, line);
}

// ==== cstr_eq ====
void __assert_cstr_eq__(const char* x, const char* y, const char* condition, const char* file, int line)
{
  if(LIKELY((strcmp(x,y) == 0)))
    return;
  else
  __bin_assert_failed__(condition, (x), (y), file, line);
}

// ==== str_eq ====
void __assert_str_eq__(str x, str y, const char* condition, const char* file, int line)
{
  if(LIKELY((str_cmp(x,y) == 0)))
    return;
  else
  __bin_assert_failed__(condition, str_fmt(x), str_fmt(y), file, line);
}

// ==== bool_eq ====
void __assert_bool_eq__(bool x, bool y, const char* condition, const char* file, int line)
{
  if(LIKELY(x == y))
    return;
  else
  __bin_assert_failed__(condition, fmt_bool(x), fmt_bool(y), file, line);
}

#endif // __FRAMAC__
