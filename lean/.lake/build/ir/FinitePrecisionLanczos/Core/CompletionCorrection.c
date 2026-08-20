// Lean compiler output
// Module: FinitePrecisionLanczos.Core.CompletionCorrection
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Lanczos.Greenbaum.Dilation
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
lean_object* lp_mathlib_Matrix_transpose___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___closed__0 = (const lean_object*)&lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__0(lean_object* v_X_1_, lean_object* v_a_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lp_mathlib_Matrix_transpose___redArg(v_X_1_, v_j_3_, v_a_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__1(lean_object* v_E_5_, lean_object* v_a_6_, lean_object* v_j_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_2(v_E_5_, v_a_6_, v_j_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__2(lean_object* v_E_9_, lean_object* v_a_10_, lean_object* v_j_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_mathlib_Matrix_transpose___redArg(v_E_9_, v_j_11_, v_a_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__3(lean_object* v_X_13_, lean_object* v_a_14_, lean_object* v_j_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_apply_2(v_X_13_, v_a_14_, v_j_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__6(lean_object* v_E_17_, lean_object* v_j_18_, lean_object* v_j_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_apply_2(v_E_17_, v_j_19_, v_j_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__4(lean_object* v_X_21_, lean_object* v_j_22_, lean_object* v_j_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_mathlib_Matrix_transpose___redArg(v_X_21_, v_j_22_, v_j_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__5(lean_object* v_X_25_, lean_object* v_inst_26_, lean_object* v___x_27_, lean_object* v___x_28_, lean_object* v___f_29_, lean_object* v_j_30_){
_start:
{
lean_object* v___f_31_; lean_object* v___x_32_; 
v___f_31_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__4), 3, 2);
lean_closure_set(v___f_31_, 0, v_X_25_);
lean_closure_set(v___f_31_, 1, v_j_30_);
v___x_32_ = lp_mathlib_dotProduct___redArg(v_inst_26_, v___x_27_, v___x_28_, v___f_31_, v___f_29_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__5___boxed(lean_object* v_X_33_, lean_object* v_inst_34_, lean_object* v___x_35_, lean_object* v___x_36_, lean_object* v___f_37_, lean_object* v_j_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__5(v_X_33_, v_inst_34_, v___x_35_, v___x_36_, v___f_37_, v_j_38_);
lean_dec_ref(v___x_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__7(lean_object* v_E_40_, lean_object* v_X_41_, lean_object* v_inst_42_, lean_object* v___x_43_, lean_object* v___x_44_, lean_object* v_inst_45_, lean_object* v___f_46_, lean_object* v_j_47_){
_start:
{
lean_object* v___f_48_; lean_object* v___f_49_; lean_object* v___x_50_; 
v___f_48_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__6), 3, 2);
lean_closure_set(v___f_48_, 0, v_E_40_);
lean_closure_set(v___f_48_, 1, v_j_47_);
lean_inc_ref(v___x_44_);
lean_inc(v___x_43_);
v___f_49_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_49_, 0, v_X_41_);
lean_closure_set(v___f_49_, 1, v_inst_42_);
lean_closure_set(v___f_49_, 2, v___x_43_);
lean_closure_set(v___f_49_, 3, v___x_44_);
lean_closure_set(v___f_49_, 4, v___f_48_);
v___x_50_ = lp_mathlib_dotProduct___redArg(v_inst_45_, v___x_43_, v___x_44_, v___f_46_, v___f_49_);
lean_dec_ref(v___x_44_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg(lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_X_54_, lean_object* v_E_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___f_58_; lean_object* v___f_59_; lean_object* v___f_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___f_64_; lean_object* v___x_65_; lean_object* v___f_66_; lean_object* v___x_67_; lean_object* v___f_68_; lean_object* v___f_69_; lean_object* v___x_70_; lean_object* v___f_71_; 
lean_inc(v_a_57_);
lean_inc_n(v_X_54_, 2);
v___f_58_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__0), 3, 2);
lean_closure_set(v___f_58_, 0, v_X_54_);
lean_closure_set(v___f_58_, 1, v_a_57_);
lean_inc(v_a_56_);
lean_inc_n(v_E_55_, 2);
v___f_59_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__1), 3, 2);
lean_closure_set(v___f_59_, 0, v_E_55_);
lean_closure_set(v___f_59_, 1, v_a_56_);
v___f_60_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__2), 3, 2);
lean_closure_set(v___f_60_, 0, v_E_55_);
lean_closure_set(v___f_60_, 1, v_a_57_);
v___f_61_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__3), 3, 2);
lean_closure_set(v___f_61_, 0, v_X_54_);
lean_closure_set(v___f_61_, 1, v_a_56_);
v___x_62_ = ((lean_object*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___closed__0));
v___x_63_ = lp_mathlib_Real_instAddCommMonoid;
lean_inc_ref(v___f_61_);
lean_inc_n(v_inst_53_, 3);
v___f_64_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg___lam__7), 8, 7);
lean_closure_set(v___f_64_, 0, v_E_55_);
lean_closure_set(v___f_64_, 1, v_X_54_);
lean_closure_set(v___f_64_, 2, v_inst_52_);
lean_closure_set(v___f_64_, 3, v___x_62_);
lean_closure_set(v___f_64_, 4, v___x_63_);
lean_closure_set(v___f_64_, 5, v_inst_53_);
lean_closure_set(v___f_64_, 6, v___f_61_);
lean_inc_ref(v___f_58_);
v___x_65_ = lp_mathlib_dotProduct___redArg(v_inst_53_, v___x_62_, v___x_63_, v___f_59_, v___f_58_);
v___f_66_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_66_, 0, v___x_65_);
v___x_67_ = lp_mathlib_dotProduct___redArg(v_inst_53_, v___x_62_, v___x_63_, v___f_61_, v___f_60_);
v___f_68_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_68_, 0, v___x_67_);
v___f_69_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_69_, 0, v___f_66_);
lean_closure_set(v___f_69_, 1, v___f_68_);
v___x_70_ = lp_mathlib_dotProduct___redArg(v_inst_53_, v___x_62_, v___x_63_, v___f_64_, v___f_58_);
v___f_71_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_71_, 0, v___f_69_);
lean_closure_set(v___f_71_, 1, v___x_70_);
return v___f_71_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection(lean_object* v_I_72_, lean_object* v_J_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_X_76_, lean_object* v_E_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_symmetricCorrection___redArg(v_inst_74_, v_inst_75_, v_X_76_, v_E_77_, v_a_78_, v_a_79_);
return v___x_80_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Greenbaum_Dilation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_CompletionCorrection(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Greenbaum_Dilation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
