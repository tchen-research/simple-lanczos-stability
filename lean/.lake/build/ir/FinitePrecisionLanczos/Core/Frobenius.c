// Lean compiler output
// Module: FinitePrecisionLanczos.Core.Frobenius
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Core.Matrix
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* l_npowRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg___closed__0 = (const lean_object*)&lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg___lam__0(lean_object* v_X_1_, lean_object* v_a_2_, lean_object* v___f_3_, lean_object* v_b_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_apply_2(v_X_1_, v_a_2_, v_b_4_);
v___x_6_ = lean_unsigned_to_nat(2u);
v___x_7_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_8_ = l_npowRec___redArg(v___x_7_, v___f_3_, v___x_6_, v___x_5_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg___lam__1(lean_object* v_X_9_, lean_object* v___f_10_, lean_object* v___x_11_, lean_object* v_inst_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___f_14_; lean_object* v___x_15_; 
v___f_14_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg___lam__0), 4, 3);
lean_closure_set(v___f_14_, 0, v_X_9_);
lean_closure_set(v___f_14_, 1, v_a_13_);
lean_closure_set(v___f_14_, 2, v___f_10_);
v___x_15_ = lp_mathlib_Finset_sum___redArg(v___x_11_, v_inst_12_, v___f_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg___lam__1___boxed(lean_object* v_X_16_, lean_object* v___f_17_, lean_object* v___x_18_, lean_object* v_inst_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg___lam__1(v_X_16_, v___f_17_, v___x_18_, v_inst_19_, v_a_20_);
lean_dec_ref(v___x_18_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg(lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_X_25_){
_start:
{
lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_26_ = ((lean_object*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg___closed__0));
v___x_27_ = lp_mathlib_Real_instAddCommMonoid;
v___f_28_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_28_, 0, v_X_25_);
lean_closure_set(v___f_28_, 1, v___f_26_);
lean_closure_set(v___f_28_, 2, v___x_27_);
lean_closure_set(v___f_28_, 3, v_inst_24_);
v___x_29_ = lp_mathlib_Finset_sum___redArg(v___x_27_, v_inst_23_, v___f_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq(lean_object* v_00_u03b9_30_, lean_object* v_00_u03ba_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_X_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_frobSq___redArg(v_inst_32_, v_inst_33_, v_X_34_);
return v___x_35_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Matrix(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Frobenius(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Matrix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
