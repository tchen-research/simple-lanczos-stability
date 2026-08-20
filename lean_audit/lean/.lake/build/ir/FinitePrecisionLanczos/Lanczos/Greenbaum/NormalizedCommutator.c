// Lean compiler output
// Module: FinitePrecisionLanczos.Lanczos.Greenbaum.NormalizedCommutator
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Lanczos.Greenbaum.NormalizedRecurrence
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
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Amat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_Cmat_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_rawUpperError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_rawUpperError(lean_object* v_n_1_, lean_object* v_k_2_, lean_object* v_L_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___f_8_; lean_object* v___f_9_; 
lean_inc(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_L_3_);
lean_inc(v_k_2_);
lean_inc_n(v_n_1_, 2);
v___x_6_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Amat(v_n_1_, v_k_2_, v_L_3_, v_a_4_, v_a_5_);
v___x_7_ = lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_Cmat_spec__0(v_n_1_, v_k_2_, v_L_3_, v_a_4_, v_a_5_, v_n_1_);
v___f_8_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_8_, 0, v___x_7_);
v___f_9_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_9_, 0, v___x_6_);
lean_closure_set(v___f_9_, 1, v___f_8_);
return v___f_9_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Greenbaum_NormalizedRecurrence(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Greenbaum_NormalizedCommutator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Greenbaum_NormalizedRecurrence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
