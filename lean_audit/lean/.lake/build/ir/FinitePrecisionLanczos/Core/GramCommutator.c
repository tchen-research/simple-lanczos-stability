// Lean compiler output
// Module: FinitePrecisionLanczos.Core.GramCommutator
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Core.Commutator public import FinitePrecisionLanczos.Core.DilationRecurrence
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
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_GramRecurrence_col___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_GramRecurrence_col(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_GramRecurrence_col___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_GramRecurrence_col___redArg(lean_object* v_G_1_, lean_object* v_j_2_, lean_object* v_r_3_){
_start:
{
lean_object* v_W_4_; lean_object* v___x_5_; 
v_W_4_ = lean_ctor_get(v_G_1_, 2);
lean_inc(v_W_4_);
lean_dec_ref(v_G_1_);
v___x_5_ = lean_apply_2(v_W_4_, v_r_3_, v_j_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_GramRecurrence_col(lean_object* v_n_6_, lean_object* v_k_7_, lean_object* v_G_8_, lean_object* v_j_9_, lean_object* v_r_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_GramRecurrence_col___redArg(v_G_8_, v_j_9_, v_r_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_GramRecurrence_col___boxed(lean_object* v_n_12_, lean_object* v_k_13_, lean_object* v_G_14_, lean_object* v_j_15_, lean_object* v_r_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_GramRecurrence_col(v_n_12_, v_k_13_, v_G_14_, v_j_15_, v_r_16_);
lean_dec(v_k_13_);
lean_dec(v_n_12_);
return v_res_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Commutator(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_DilationRecurrence(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_GramCommutator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Commutator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_DilationRecurrence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
