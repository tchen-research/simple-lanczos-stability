// Lean compiler output
// Module: FinitePrecisionLanczos.Matrix
// Imports: public import Init public meta import Init public import Mathlib.Analysis.CStarAlgebra.Matrix public import Mathlib.Analysis.Matrix.Spectrum public import Mathlib.Tactic
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
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_vdot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ofCols___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ofCols(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ofCols___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___lam__0(lean_object* v_v_1_, lean_object* v_w_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___f_6_; 
lean_inc(v_i_3_);
v___x_4_ = lean_apply_1(v_v_1_, v_i_3_);
v___x_5_ = lean_apply_1(v_w_2_, v_i_3_);
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_6_, 0, v___x_4_);
lean_closure_set(v___f_6_, 1, v___x_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0_spec__1(lean_object* v_s_8_){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___f_9_ = ((lean_object*)(lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0_spec__1___closed__0));
v___x_10_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_11_ = l_List_foldrTR___redArg(v___f_9_, v___x_10_, v_s_8_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(lean_object* v_s_12_, lean_object* v_f_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lp_mathlib_Multiset_map___redArg(v_f_13_, v_s_12_);
v___x_15_ = lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0_spec__1(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0(lean_object* v_n_16_, lean_object* v_v_17_, lean_object* v_w_18_){
_start:
{
lean_object* v___f_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___f_19_ = lean_alloc_closure((void*)(lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_19_, 0, v_v_17_);
lean_closure_set(v___f_19_, 1, v_w_18_);
v___x_20_ = l_List_finRange(v_n_16_);
v___x_21_ = lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_20_, v___f_19_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_vdot(lean_object* v_n_22_, lean_object* v_x_23_, lean_object* v_y_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0(v_n_22_, v_x_23_, v_y_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0(lean_object* v_00_u03b9_26_, lean_object* v_s_27_, lean_object* v_f_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v_s_27_, v_f_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ofCols___redArg(lean_object* v_q_30_, lean_object* v_i_31_, lean_object* v_j_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_apply_2(v_q_30_, v_j_32_, v_i_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ofCols(lean_object* v_n_34_, lean_object* v_k_35_, lean_object* v_q_36_, lean_object* v_i_37_, lean_object* v_j_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_apply_2(v_q_36_, v_j_38_, v_i_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ofCols___boxed(lean_object* v_n_40_, lean_object* v_k_41_, lean_object* v_q_42_, lean_object* v_i_43_, lean_object* v_j_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_Paige_FinitePrecisionLanczos_ofCols(v_n_40_, v_k_41_, v_q_42_, v_i_43_, v_j_44_);
lean_dec(v_k_41_);
lean_dec(v_n_40_);
return v_res_45_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_CStarAlgebra_Matrix(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Matrix_Spectrum(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Paige_FinitePrecisionLanczos_Matrix(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_CStarAlgebra_Matrix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Matrix_Spectrum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
