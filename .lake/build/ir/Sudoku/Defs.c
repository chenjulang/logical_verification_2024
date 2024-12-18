// Lean compiler output
// Module: Sudoku.Defs
// Imports: Init Mathlib.Tactic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_reg__coords___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Progress_get___boxed(lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_reg__coords(lean_object*, lean_object*);
lean_object* l_List_setTR_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Progress_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Progress_set_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_mul(lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_Progress_set_x27___closed__1;
LEAN_EXPORT lean_object* l_reg__coords(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_div(x_1, x_3);
x_5 = lean_unsigned_to_nat(4u);
x_6 = l_Fin_mul(x_5, x_4, x_3);
lean_dec(x_4);
x_7 = lean_nat_div(x_2, x_3);
x_8 = l_Fin_add(x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_nat_mod(x_1, x_3);
x_10 = l_Fin_mul(x_5, x_9, x_3);
lean_dec(x_9);
x_11 = lean_nat_mod(x_2, x_3);
x_12 = l_Fin_add(x_5, x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_reg__coords___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_reg__coords(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Progress_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l_List_get_x21___rarg(x_4, x_1, x_5);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_List_get_x21___rarg(x_3, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Progress_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Progress_get(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Progress_set_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Progress_set_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_box(0);
lean_inc(x_4);
x_6 = l_List_get_x21___rarg(x_5, x_1, x_4);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Progress_set_x27___closed__1;
lean_inc(x_6);
x_9 = l_List_setTR_go___rarg(x_6, x_3, x_6, x_7, x_8);
lean_inc(x_1);
x_10 = l_List_setTR_go___rarg(x_1, x_9, x_1, x_4, x_8);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Sudoku_Defs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Progress_set_x27___closed__1 = _init_l_Progress_set_x27___closed__1();
lean_mark_persistent(l_Progress_set_x27___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
