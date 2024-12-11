// Lean compiler output
// Module: LoVe.LoVe04_ForwardProofs_Demo
// Imports: Init LoVe.LoVe02_ProgramsAndTheorems_Demo
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
LEAN_EXPORT lean_object* l___private_LoVe_LoVe04__ForwardProofs__Demo_0__LoVe_reverse_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LoVe_LoVe04__ForwardProofs__Demo_0__LoVe_reverse_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_ForwardProofs_double(lean_object*);
LEAN_EXPORT lean_object* l_LoVe_ForwardProofs_double___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LoVe_LoVe04__ForwardProofs__Demo_0__LoVe_reverse_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_ForwardProofs_double(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_add(x_1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LoVe_ForwardProofs_double___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_LoVe_ForwardProofs_double(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_LoVe_LoVe04__ForwardProofs__Demo_0__LoVe_reverse_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_LoVe_LoVe04__ForwardProofs__Demo_0__LoVe_reverse_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_LoVe_LoVe04__ForwardProofs__Demo_0__LoVe_reverse_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_LoVe_LoVe04__ForwardProofs__Demo_0__LoVe_reverse_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_LoVe_LoVe04__ForwardProofs__Demo_0__LoVe_reverse_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LoVe_LoVe02__ProgramsAndTheorems__Demo(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LoVe_LoVe04__ForwardProofs__Demo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LoVe_LoVe02__ProgramsAndTheorems__Demo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif