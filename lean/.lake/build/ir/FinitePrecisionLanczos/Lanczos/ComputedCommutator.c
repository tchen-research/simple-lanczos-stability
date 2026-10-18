// Lean compiler output
// Module: FinitePrecisionLanczos.Lanczos.ComputedCommutator
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Lanczos.Ritz public import FinitePrecisionLanczos.Core.SaadGramCommutator
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_g___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vmat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transpose___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vmat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_FinitePrecisionLanczos_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Tmat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vsucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Fmat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_computedR_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_computedR_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_computedR_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_computedR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_computedSaad___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_computedSaad___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_computedSaad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_computedR_spec__0___lam__0(lean_object* v___x_1_, lean_object* v_i_2_, lean_object* v_L_3_, lean_object* v_j_4_, lean_object* v_i_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___f_8_; 
lean_inc(v_i_5_);
v___x_6_ = lp_mathlib_Matrix_transpose___redArg(v___x_1_, v_i_2_, v_i_5_);
v___x_7_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vmat___redArg(v_L_3_, v_i_5_, v_j_4_);
v___f_8_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_8_, 0, v___x_6_);
lean_closure_set(v___f_8_, 1, v___x_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_computedR_spec__0___lam__0___boxed(lean_object* v___x_9_, lean_object* v_i_10_, lean_object* v_L_11_, lean_object* v_j_12_, lean_object* v_i_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_computedR_spec__0___lam__0(v___x_9_, v_i_10_, v_L_11_, v_j_12_, v_i_13_);
lean_dec(v_j_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_computedR_spec__0(lean_object* v_n_15_, lean_object* v_k_16_, lean_object* v_L_17_, lean_object* v_i_18_, lean_object* v_j_19_, lean_object* v_n_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___f_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
lean_inc_ref(v_L_17_);
v___x_21_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vmat___boxed), 5, 3);
lean_closure_set(v___x_21_, 0, v_n_15_);
lean_closure_set(v___x_21_, 1, v_k_16_);
lean_closure_set(v___x_21_, 2, v_L_17_);
v___f_22_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_computedR_spec__0___lam__0___boxed), 5, 4);
lean_closure_set(v___f_22_, 0, v___x_21_);
lean_closure_set(v___f_22_, 1, v_i_18_);
lean_closure_set(v___f_22_, 2, v_L_17_);
lean_closure_set(v___f_22_, 3, v_j_19_);
v___x_23_ = l_List_finRange(v_n_20_);
v___x_24_ = lp_FinitePrecisionLanczos_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_23_, v___f_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_computedR(lean_object* v_n_25_, lean_object* v_k_26_, lean_object* v_L_27_, lean_object* v_i_28_, lean_object* v_j_29_){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = lean_nat_dec_lt(v_i_28_, v_j_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; 
lean_dec(v_j_29_);
lean_dec(v_i_28_);
lean_dec_ref(v_L_27_);
lean_dec(v_k_26_);
lean_dec(v_n_25_);
v___x_31_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_31_;
}
else
{
lean_object* v___x_32_; 
lean_inc(v_n_25_);
v___x_32_ = lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_computedR_spec__0(v_n_25_, v_k_26_, v_L_27_, v_i_28_, v_j_29_, v_n_25_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_computedSaad___lam__0(lean_object* v_n_33_, lean_object* v_L_34_, lean_object* v_j_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_unsigned_to_nat(1u);
v___x_37_ = lean_nat_add(v_j_35_, v___x_36_);
v___x_38_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_g___redArg(v_n_33_, v_L_34_, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_computedSaad___lam__0___boxed(lean_object* v_n_39_, lean_object* v_L_40_, lean_object* v_j_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_computedSaad___lam__0(v_n_39_, v_L_40_, v_j_41_);
lean_dec(v_j_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_computedSaad(lean_object* v_n_43_, lean_object* v_k_44_, lean_object* v_L_45_){
_start:
{
lean_object* v_H_46_; lean_object* v_00_u03b2_47_; lean_object* v___f_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_H_46_ = lean_ctor_get(v_L_45_, 0);
lean_inc(v_H_46_);
v_00_u03b2_47_ = lean_ctor_get(v_L_45_, 6);
lean_inc_ref_n(v_L_45_, 4);
lean_inc_n(v_n_43_, 4);
v___f_48_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_computedSaad___lam__0___boxed), 3, 2);
lean_closure_set(v___f_48_, 0, v_n_43_);
lean_closure_set(v___f_48_, 1, v_L_45_);
lean_inc_n(v_k_44_, 4);
v___x_49_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Tmat___boxed), 5, 3);
lean_closure_set(v___x_49_, 0, v_n_43_);
lean_closure_set(v___x_49_, 1, v_k_44_);
lean_closure_set(v___x_49_, 2, v_L_45_);
lean_inc(v_00_u03b2_47_);
v___x_50_ = lean_apply_1(v_00_u03b2_47_, v_k_44_);
v___x_51_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vsucc___boxed), 5, 3);
lean_closure_set(v___x_51_, 0, v_n_43_);
lean_closure_set(v___x_51_, 1, v_k_44_);
lean_closure_set(v___x_51_, 2, v_L_45_);
v___x_52_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Fmat___boxed), 5, 3);
lean_closure_set(v___x_52_, 0, v_n_43_);
lean_closure_set(v___x_52_, 1, v_k_44_);
lean_closure_set(v___x_52_, 2, v_L_45_);
v___x_53_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_computedR), 5, 3);
lean_closure_set(v___x_53_, 0, v_n_43_);
lean_closure_set(v___x_53_, 1, v_k_44_);
lean_closure_set(v___x_53_, 2, v_L_45_);
v___x_54_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_54_, 0, v_H_46_);
lean_ctor_set(v___x_54_, 1, v___x_49_);
lean_ctor_set(v___x_54_, 2, v___x_50_);
lean_ctor_set(v___x_54_, 3, v___x_51_);
lean_ctor_set(v___x_54_, 4, v___x_52_);
lean_ctor_set(v___x_54_, 5, v___x_53_);
lean_ctor_set(v___x_54_, 6, v___f_48_);
return v___x_54_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Ritz(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_SaadGramCommutator(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_ComputedCommutator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Ritz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_SaadGramCommutator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
