// Copyright (c) 2024 Robert Hildebrandt. All rights reserved.
// >> AUTOGENERATED!!! << NO NOT MODIFY! >> Modifications will be overwritten!!
// ==== usize ====
//@ terminates true; assigns \nothing; exits false; admit ensures x == y;
void __assert_usize_eq__(usize x, usize y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x != y;
void __assert_usize_ne__(usize x, usize y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x < y;
void __assert_usize_lt__(usize x, usize y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x <= y;
void __assert_usize_lte__(usize x, usize y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x > y;
void __assert_usize_gt__(usize x, usize y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x >= y;
void __assert_usize_gte__(usize x, usize y, const char* condition, const char* file, int line);

//@ terminates true; assigns \nothing; exits false; admit ensures x <= y <= z;
void __assert_usize_lte_lte__(usize x, usize y, usize z, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x <= y < z;
void __assert_usize_lte_lt__(usize x, usize y, usize z, const char* condition, const char* file, int line);

// ==== ssize ====
//@ terminates true; assigns \nothing; exits false; admit ensures x == y;
void __assert_ssize_eq__(ssize x, ssize y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x != y;
void __assert_ssize_ne__(ssize x, ssize y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x < y;
void __assert_ssize_lt__(ssize x, ssize y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x <= y;
void __assert_ssize_lte__(ssize x, ssize y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x > y;
void __assert_ssize_gt__(ssize x, ssize y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x >= y;
void __assert_ssize_gte__(ssize x, ssize y, const char* condition, const char* file, int line);

//@ terminates true; assigns \nothing; exits false; admit ensures x <= y <= z;
void __assert_ssize_lte_lte__(ssize x, ssize y, ssize z, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x <= y < z;
void __assert_ssize_lte_lt__(ssize x, ssize y, ssize z, const char* condition, const char* file, int line);

// ==== int ====
//@ terminates true; assigns \nothing; exits false; admit ensures x == y;
void __assert_int_eq__(int x, int y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x != y;
void __assert_int_ne__(int x, int y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x < y;
void __assert_int_lt__(int x, int y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x <= y;
void __assert_int_lte__(int x, int y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x > y;
void __assert_int_gt__(int x, int y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x >= y;
void __assert_int_gte__(int x, int y, const char* condition, const char* file, int line);

// ==== char ====
//@ terminates true; assigns \nothing; exits false; admit ensures x == y;
void __assert_char_eq__(char x, char y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x != y;
void __assert_char_ne__(char x, char y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x < y;
void __assert_char_lt__(char x, char y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x <= y;
void __assert_char_lte__(char x, char y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x > y;
void __assert_char_gt__(char x, char y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x >= y;
void __assert_char_gte__(char x, char y, const char* condition, const char* file, int line);

// ==== ptr ====
//@ terminates true; assigns \nothing; exits false; admit ensures x == y;
void __assert_ptr_eq__(const void* x, const void* y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x != y;
void __assert_ptr_ne__(const void* x, const void* y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x < y;
void __assert_ptr_lt__(const void* x, const void* y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x <= y;
void __assert_ptr_lte__(const void* x, const void* y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x > y;
void __assert_ptr_gt__(const void* x, const void* y, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x >= y;
void __assert_ptr_gte__(const void* x, const void* y, const char* condition, const char* file, int line);

//@ terminates true; assigns \nothing; exits false; admit ensures x <= y <= z;
void __assert_ptr_lte_lte__(const void* x, const void* y, const void* z, const char* condition, const char* file, int line);
//@ terminates true; assigns \nothing; exits false; admit ensures x <= y < z;
void __assert_ptr_lte_lt__(const void* x, const void* y, const void* z, const char* condition, const char* file, int line);

// ==== cstr_eq ====
//@ terminates true; assigns \nothing; exits false;
void __assert_cstr_eq__(const char* x, const char* y, const char* condition, const char* file, int line);

// ==== str_eq ====
//@ terminates true; assigns \nothing; exits false;
void __assert_str_eq__(str x, str y, const char* condition, const char* file, int line);

// ==== bool_eq ====
//@ terminates true; assigns \nothing; exits false; admit ensures x == y;
void __assert_bool_eq__(bool x, bool y, const char* condition, const char* file, int line);

// ==== usize ====
#define assert_usize_eq(x, y) __assert_usize_eq__(x, y, #x " == " #y, __FILE__, __LINE__)
#define assert_usize_ne(x, y) __assert_usize_ne__(x, y, #x " != " #y, __FILE__, __LINE__)
#define assert_usize_lt(x, y) __assert_usize_lt__(x, y, #x " < " #y, __FILE__, __LINE__)
#define assert_usize_lte(x, y) __assert_usize_lte__(x, y, #x " <= " #y, __FILE__, __LINE__)
#define assert_usize_gt(x, y) __assert_usize_gt__(x, y, #x " > " #y, __FILE__, __LINE__)
#define assert_usize_gte(x, y) __assert_usize_gte__(x, y, #x " >= " #y, __FILE__, __LINE__)

#define assert_usize_lte_lte(x, y, z) __assert_usize_lte_lte__(x, y, z, #x " <= " #y " <= " #z, __FILE__, __LINE__)
#define assert_usize_lte_lt(x, y, z) __assert_usize_lte_lt__(x, y, z, #x " <= " #y " < " #z, __FILE__, __LINE__)

// ==== ssize ====
#define assert_ssize_eq(x, y) __assert_ssize_eq__(x, y, #x " == " #y, __FILE__, __LINE__)
#define assert_ssize_ne(x, y) __assert_ssize_ne__(x, y, #x " != " #y, __FILE__, __LINE__)
#define assert_ssize_lt(x, y) __assert_ssize_lt__(x, y, #x " < " #y, __FILE__, __LINE__)
#define assert_ssize_lte(x, y) __assert_ssize_lte__(x, y, #x " <= " #y, __FILE__, __LINE__)
#define assert_ssize_gt(x, y) __assert_ssize_gt__(x, y, #x " > " #y, __FILE__, __LINE__)
#define assert_ssize_gte(x, y) __assert_ssize_gte__(x, y, #x " >= " #y, __FILE__, __LINE__)

#define assert_ssize_lte_lte(x, y, z) __assert_ssize_lte_lte__(x, y, z, #x " <= " #y " <= " #z, __FILE__, __LINE__)
#define assert_ssize_lte_lt(x, y, z) __assert_ssize_lte_lt__(x, y, z, #x " <= " #y " < " #z, __FILE__, __LINE__)

// ==== int ====
#define assert_int_eq(x, y) __assert_int_eq__(x, y, #x " == " #y, __FILE__, __LINE__)
#define assert_int_ne(x, y) __assert_int_ne__(x, y, #x " != " #y, __FILE__, __LINE__)
#define assert_int_lt(x, y) __assert_int_lt__(x, y, #x " < " #y, __FILE__, __LINE__)
#define assert_int_lte(x, y) __assert_int_lte__(x, y, #x " <= " #y, __FILE__, __LINE__)
#define assert_int_gt(x, y) __assert_int_gt__(x, y, #x " > " #y, __FILE__, __LINE__)
#define assert_int_gte(x, y) __assert_int_gte__(x, y, #x " >= " #y, __FILE__, __LINE__)

// ==== char ====
#define assert_char_eq(x, y) __assert_char_eq__(x, y, #x " == " #y, __FILE__, __LINE__)
#define assert_char_ne(x, y) __assert_char_ne__(x, y, #x " != " #y, __FILE__, __LINE__)
#define assert_char_lt(x, y) __assert_char_lt__(x, y, #x " < " #y, __FILE__, __LINE__)
#define assert_char_lte(x, y) __assert_char_lte__(x, y, #x " <= " #y, __FILE__, __LINE__)
#define assert_char_gt(x, y) __assert_char_gt__(x, y, #x " > " #y, __FILE__, __LINE__)
#define assert_char_gte(x, y) __assert_char_gte__(x, y, #x " >= " #y, __FILE__, __LINE__)

// ==== ptr ====
#define assert_ptr_eq(x, y) __assert_ptr_eq__(x, y, #x " == " #y, __FILE__, __LINE__)
#define assert_ptr_ne(x, y) __assert_ptr_ne__(x, y, #x " != " #y, __FILE__, __LINE__)
#define assert_ptr_lt(x, y) __assert_ptr_lt__(x, y, #x " < " #y, __FILE__, __LINE__)
#define assert_ptr_lte(x, y) __assert_ptr_lte__(x, y, #x " <= " #y, __FILE__, __LINE__)
#define assert_ptr_gt(x, y) __assert_ptr_gt__(x, y, #x " > " #y, __FILE__, __LINE__)
#define assert_ptr_gte(x, y) __assert_ptr_gte__(x, y, #x " >= " #y, __FILE__, __LINE__)

#define assert_ptr_lte_lte(x, y, z) __assert_ptr_lte_lte__(x, y, z, #x " <= " #y " <= " #z, __FILE__, __LINE__)
#define assert_ptr_lte_lt(x, y, z) __assert_ptr_lte_lt__(x, y, z, #x " <= " #y " < " #z, __FILE__, __LINE__)

// ==== cstr_eq ====
#define assert_cstr_eq(x, y) __assert_cstr_eq__(x, y, #x " == " #y, __FILE__, __LINE__)

// ==== str_eq ====
#define assert_str_eq(x, y) __assert_str_eq__(x, y, #x " == " #y, __FILE__, __LINE__)

// ==== bool_eq ====
#define assert_bool_eq(x, y) __assert_bool_eq__(x, y, #x " == " #y, __FILE__, __LINE__)

#if defined(__FRAMAC__) || !ENV_DEBUG
// ==== usize ====
#define debug_assert_usize_eq(x, y)
#define debug_assert_usize_ne(x, y)
#define debug_assert_usize_lt(x, y)
#define debug_assert_usize_lte(x, y)
#define debug_assert_usize_gt(x, y)
#define debug_assert_usize_gte(x, y)

#define debug_assert_usize_lte_lte(x, y, z)
#define debug_assert_usize_lte_lt(x, y, z)

// ==== ssize ====
#define debug_assert_ssize_eq(x, y)
#define debug_assert_ssize_ne(x, y)
#define debug_assert_ssize_lt(x, y)
#define debug_assert_ssize_lte(x, y)
#define debug_assert_ssize_gt(x, y)
#define debug_assert_ssize_gte(x, y)

#define debug_assert_ssize_lte_lte(x, y, z)
#define debug_assert_ssize_lte_lt(x, y, z)

// ==== int ====
#define debug_assert_int_eq(x, y)
#define debug_assert_int_ne(x, y)
#define debug_assert_int_lt(x, y)
#define debug_assert_int_lte(x, y)
#define debug_assert_int_gt(x, y)
#define debug_assert_int_gte(x, y)

// ==== char ====
#define debug_assert_char_eq(x, y)
#define debug_assert_char_ne(x, y)
#define debug_assert_char_lt(x, y)
#define debug_assert_char_lte(x, y)
#define debug_assert_char_gt(x, y)
#define debug_assert_char_gte(x, y)

// ==== ptr ====
#define debug_assert_ptr_eq(x, y)
#define debug_assert_ptr_ne(x, y)
#define debug_assert_ptr_lt(x, y)
#define debug_assert_ptr_lte(x, y)
#define debug_assert_ptr_gt(x, y)
#define debug_assert_ptr_gte(x, y)

#define debug_assert_ptr_lte_lte(x, y, z)
#define debug_assert_ptr_lte_lt(x, y, z)

// ==== cstr_eq ====
#define debug_assert_cstr_eq(x, y)

// ==== str_eq ====
#define debug_assert_str_eq(x, y)

// ==== bool_eq ====
#define debug_assert_bool_eq(x, y)

#else // __FRAMAC__ || !ENV_DEBUG
// ==== usize ====
#define debug_assert_usize_eq(x, y) __assert_usize_eq__(x, y, #x " == " #y, __FILE__, __LINE__)
#define debug_assert_usize_ne(x, y) __assert_usize_ne__(x, y, #x " != " #y, __FILE__, __LINE__)
#define debug_assert_usize_lt(x, y) __assert_usize_lt__(x, y, #x " < " #y, __FILE__, __LINE__)
#define debug_assert_usize_lte(x, y) __assert_usize_lte__(x, y, #x " <= " #y, __FILE__, __LINE__)
#define debug_assert_usize_gt(x, y) __assert_usize_gt__(x, y, #x " > " #y, __FILE__, __LINE__)
#define debug_assert_usize_gte(x, y) __assert_usize_gte__(x, y, #x " >= " #y, __FILE__, __LINE__)

#define debug_assert_usize_lte_lte(x, y, z) __assert_usize_lte_lte__(x, y, z, #x " <= " #y " <= " #z, __FILE__, __LINE__)
#define debug_assert_usize_lte_lt(x, y, z) __assert_usize_lte_lt__(x, y, z, #x " <= " #y " < " #z, __FILE__, __LINE__)

// ==== ssize ====
#define debug_assert_ssize_eq(x, y) __assert_ssize_eq__(x, y, #x " == " #y, __FILE__, __LINE__)
#define debug_assert_ssize_ne(x, y) __assert_ssize_ne__(x, y, #x " != " #y, __FILE__, __LINE__)
#define debug_assert_ssize_lt(x, y) __assert_ssize_lt__(x, y, #x " < " #y, __FILE__, __LINE__)
#define debug_assert_ssize_lte(x, y) __assert_ssize_lte__(x, y, #x " <= " #y, __FILE__, __LINE__)
#define debug_assert_ssize_gt(x, y) __assert_ssize_gt__(x, y, #x " > " #y, __FILE__, __LINE__)
#define debug_assert_ssize_gte(x, y) __assert_ssize_gte__(x, y, #x " >= " #y, __FILE__, __LINE__)

#define debug_assert_ssize_lte_lte(x, y, z) __assert_ssize_lte_lte__(x, y, z, #x " <= " #y " <= " #z, __FILE__, __LINE__)
#define debug_assert_ssize_lte_lt(x, y, z) __assert_ssize_lte_lt__(x, y, z, #x " <= " #y " < " #z, __FILE__, __LINE__)

// ==== int ====
#define debug_assert_int_eq(x, y) __assert_int_eq__(x, y, #x " == " #y, __FILE__, __LINE__)
#define debug_assert_int_ne(x, y) __assert_int_ne__(x, y, #x " != " #y, __FILE__, __LINE__)
#define debug_assert_int_lt(x, y) __assert_int_lt__(x, y, #x " < " #y, __FILE__, __LINE__)
#define debug_assert_int_lte(x, y) __assert_int_lte__(x, y, #x " <= " #y, __FILE__, __LINE__)
#define debug_assert_int_gt(x, y) __assert_int_gt__(x, y, #x " > " #y, __FILE__, __LINE__)
#define debug_assert_int_gte(x, y) __assert_int_gte__(x, y, #x " >= " #y, __FILE__, __LINE__)

// ==== char ====
#define debug_assert_char_eq(x, y) __assert_char_eq__(x, y, #x " == " #y, __FILE__, __LINE__)
#define debug_assert_char_ne(x, y) __assert_char_ne__(x, y, #x " != " #y, __FILE__, __LINE__)
#define debug_assert_char_lt(x, y) __assert_char_lt__(x, y, #x " < " #y, __FILE__, __LINE__)
#define debug_assert_char_lte(x, y) __assert_char_lte__(x, y, #x " <= " #y, __FILE__, __LINE__)
#define debug_assert_char_gt(x, y) __assert_char_gt__(x, y, #x " > " #y, __FILE__, __LINE__)
#define debug_assert_char_gte(x, y) __assert_char_gte__(x, y, #x " >= " #y, __FILE__, __LINE__)

// ==== ptr ====
#define debug_assert_ptr_eq(x, y) __assert_ptr_eq__(x, y, #x " == " #y, __FILE__, __LINE__)
#define debug_assert_ptr_ne(x, y) __assert_ptr_ne__(x, y, #x " != " #y, __FILE__, __LINE__)
#define debug_assert_ptr_lt(x, y) __assert_ptr_lt__(x, y, #x " < " #y, __FILE__, __LINE__)
#define debug_assert_ptr_lte(x, y) __assert_ptr_lte__(x, y, #x " <= " #y, __FILE__, __LINE__)
#define debug_assert_ptr_gt(x, y) __assert_ptr_gt__(x, y, #x " > " #y, __FILE__, __LINE__)
#define debug_assert_ptr_gte(x, y) __assert_ptr_gte__(x, y, #x " >= " #y, __FILE__, __LINE__)

#define debug_assert_ptr_lte_lte(x, y, z) __assert_ptr_lte_lte__(x, y, z, #x " <= " #y " <= " #z, __FILE__, __LINE__)
#define debug_assert_ptr_lte_lt(x, y, z) __assert_ptr_lte_lt__(x, y, z, #x " <= " #y " < " #z, __FILE__, __LINE__)

// ==== cstr_eq ====
#define debug_assert_cstr_eq(x, y) __assert_cstr_eq__(x, y, #x " == " #y, __FILE__, __LINE__)

// ==== str_eq ====
#define debug_assert_str_eq(x, y) __assert_str_eq__(x, y, #x " == " #y, __FILE__, __LINE__)

// ==== bool_eq ====
#define debug_assert_bool_eq(x, y) __assert_bool_eq__(x, y, #x " == " #y, __FILE__, __LINE__)

#endif // __FRAMAC__ || !ENV_DEBUG
