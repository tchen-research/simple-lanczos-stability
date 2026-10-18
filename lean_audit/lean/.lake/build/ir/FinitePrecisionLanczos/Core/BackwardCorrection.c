// Lean compiler output
// Module: FinitePrecisionLanczos.Core.BackwardCorrection
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Core.Underline public import Mathlib.LinearAlgebra.Matrix.Rank public import Mathlib.Data.Matrix.ColumnRowPartitioned
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
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___closed__0 = (const lean_object*)&lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__0(lean_object* v_X_1_, lean_object* v_a_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lp_mathlib_Matrix_transpose___redArg(v_X_1_, v_j_3_, v_a_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__1(lean_object* v_E_5_, lean_object* v_a_6_, lean_object* v_j_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_2(v_E_5_, v_a_6_, v_j_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__2(lean_object* v_E_9_, lean_object* v_a_10_, lean_object* v_j_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_mathlib_Matrix_transpose___redArg(v_E_9_, v_j_11_, v_a_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__3(lean_object* v_X_13_, lean_object* v_a_14_, lean_object* v_j_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_apply_2(v_X_13_, v_a_14_, v_j_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__6(lean_object* v_X_17_, lean_object* v_j_18_, lean_object* v_j_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_apply_2(v_X_17_, v_j_19_, v_j_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__4(lean_object* v_X_21_, lean_object* v_j_22_, lean_object* v_j_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_mathlib_Matrix_transpose___redArg(v_X_21_, v_j_22_, v_j_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__5(lean_object* v_A_25_, lean_object* v_j_26_, lean_object* v_j_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_apply_2(v_A_25_, v_j_27_, v_j_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__7(lean_object* v_A_29_, lean_object* v_inst_30_, lean_object* v___x_31_, lean_object* v___x_32_, lean_object* v___f_33_, lean_object* v_j_34_){
_start:
{
lean_object* v___f_35_; lean_object* v___x_36_; 
v___f_35_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__5), 3, 2);
lean_closure_set(v___f_35_, 0, v_A_29_);
lean_closure_set(v___f_35_, 1, v_j_34_);
v___x_36_ = lp_mathlib_dotProduct___redArg(v_inst_30_, v___x_31_, v___x_32_, v___f_33_, v___f_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__7___boxed(lean_object* v_A_37_, lean_object* v_inst_38_, lean_object* v___x_39_, lean_object* v___x_40_, lean_object* v___f_41_, lean_object* v_j_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__7(v_A_37_, v_inst_38_, v___x_39_, v___x_40_, v___f_41_, v_j_42_);
lean_dec_ref(v___x_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__8(lean_object* v_X_44_, lean_object* v_A_45_, lean_object* v_inst_46_, lean_object* v___x_47_, lean_object* v___x_48_, lean_object* v___f_49_, lean_object* v_T_50_, lean_object* v_j_51_, lean_object* v_j_52_){
_start:
{
lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___f_57_; lean_object* v___f_58_; 
lean_inc(v_j_52_);
v___f_53_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__4), 3, 2);
lean_closure_set(v___f_53_, 0, v_X_44_);
lean_closure_set(v___f_53_, 1, v_j_52_);
lean_inc_ref(v___x_48_);
lean_inc(v___x_47_);
lean_inc(v_inst_46_);
v___f_54_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_54_, 0, v_A_45_);
lean_closure_set(v___f_54_, 1, v_inst_46_);
lean_closure_set(v___f_54_, 2, v___x_47_);
lean_closure_set(v___f_54_, 3, v___x_48_);
lean_closure_set(v___f_54_, 4, v___f_53_);
v___x_55_ = lp_mathlib_dotProduct___redArg(v_inst_46_, v___x_47_, v___x_48_, v___f_54_, v___f_49_);
lean_dec_ref(v___x_48_);
v___x_56_ = lean_apply_2(v_T_50_, v_j_52_, v_j_51_);
v___f_57_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_57_, 0, v___x_56_);
v___f_58_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_58_, 0, v___x_55_);
lean_closure_set(v___f_58_, 1, v___f_57_);
return v___f_58_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__9(lean_object* v_X_59_, lean_object* v_A_60_, lean_object* v_inst_61_, lean_object* v___x_62_, lean_object* v___x_63_, lean_object* v_T_64_, lean_object* v___x_65_, lean_object* v___f_66_, lean_object* v_j_67_){
_start:
{
lean_object* v___f_68_; lean_object* v___f_69_; lean_object* v___x_70_; 
lean_inc(v_j_67_);
lean_inc(v_X_59_);
v___f_68_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__6), 3, 2);
lean_closure_set(v___f_68_, 0, v_X_59_);
lean_closure_set(v___f_68_, 1, v_j_67_);
lean_inc_ref(v___x_63_);
lean_inc(v___x_62_);
v___f_69_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__8), 9, 8);
lean_closure_set(v___f_69_, 0, v_X_59_);
lean_closure_set(v___f_69_, 1, v_A_60_);
lean_closure_set(v___f_69_, 2, v_inst_61_);
lean_closure_set(v___f_69_, 3, v___x_62_);
lean_closure_set(v___f_69_, 4, v___x_63_);
lean_closure_set(v___f_69_, 5, v___f_68_);
lean_closure_set(v___f_69_, 6, v_T_64_);
lean_closure_set(v___f_69_, 7, v_j_67_);
v___x_70_ = lp_mathlib_dotProduct___redArg(v___x_65_, v___x_62_, v___x_63_, v___f_66_, v___f_69_);
lean_dec_ref(v___x_63_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg(lean_object* v_inst_72_, lean_object* v_k_73_, lean_object* v_A_74_, lean_object* v_X_75_, lean_object* v_E_76_, lean_object* v_T_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___f_80_; lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___f_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_95_; lean_object* v___f_96_; 
lean_inc_n(v_a_79_, 2);
lean_inc_n(v_X_75_, 2);
v___f_80_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__0), 3, 2);
lean_closure_set(v___f_80_, 0, v_X_75_);
lean_closure_set(v___f_80_, 1, v_a_79_);
lean_inc_n(v_a_78_, 2);
lean_inc(v_E_76_);
v___f_81_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__1), 3, 2);
lean_closure_set(v___f_81_, 0, v_E_76_);
lean_closure_set(v___f_81_, 1, v_a_78_);
v___f_82_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__2), 3, 2);
lean_closure_set(v___f_82_, 0, v_E_76_);
lean_closure_set(v___f_82_, 1, v_a_79_);
v___f_83_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__3), 3, 2);
lean_closure_set(v___f_83_, 0, v_X_75_);
lean_closure_set(v___f_83_, 1, v_a_78_);
v___x_84_ = ((lean_object*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___closed__0));
v___x_85_ = lp_mathlib_Real_instAddCommMonoid;
v___x_86_ = l_List_finRange(v_k_73_);
lean_inc_ref(v___f_83_);
lean_inc_n(v___x_86_, 3);
lean_inc(v_A_74_);
v___f_87_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg___lam__9), 9, 8);
lean_closure_set(v___f_87_, 0, v_X_75_);
lean_closure_set(v___f_87_, 1, v_A_74_);
lean_closure_set(v___f_87_, 2, v_inst_72_);
lean_closure_set(v___f_87_, 3, v___x_84_);
lean_closure_set(v___f_87_, 4, v___x_85_);
lean_closure_set(v___f_87_, 5, v_T_77_);
lean_closure_set(v___f_87_, 6, v___x_86_);
lean_closure_set(v___f_87_, 7, v___f_83_);
v___x_88_ = lean_apply_2(v_A_74_, v_a_78_, v_a_79_);
lean_inc_ref(v___f_80_);
v___x_89_ = lp_mathlib_dotProduct___redArg(v___x_86_, v___x_84_, v___x_85_, v___f_81_, v___f_80_);
v___f_90_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_90_, 0, v___x_89_);
v___f_91_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_91_, 0, v___x_88_);
lean_closure_set(v___f_91_, 1, v___f_90_);
v___x_92_ = lp_mathlib_dotProduct___redArg(v___x_86_, v___x_84_, v___x_85_, v___f_83_, v___f_82_);
v___f_93_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_93_, 0, v___x_92_);
v___f_94_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_94_, 0, v___f_91_);
lean_closure_set(v___f_94_, 1, v___f_93_);
v___x_95_ = lp_mathlib_dotProduct___redArg(v___x_86_, v___x_84_, v___x_85_, v___f_87_, v___f_80_);
v___f_96_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_96_, 0, v___f_94_);
lean_closure_set(v___f_96_, 1, v___x_95_);
return v___f_96_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected(lean_object* v_I_97_, lean_object* v_inst_98_, lean_object* v_k_99_, lean_object* v_A_100_, lean_object* v_X_101_, lean_object* v_E_102_, lean_object* v_T_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_backwardCorrected___redArg(v_inst_98_, v_k_99_, v_A_100_, v_X_101_, v_E_102_, v_T_103_, v_a_104_, v_a_105_);
return v___x_106_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Underline(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_Matrix_Rank(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Matrix_ColumnRowPartitioned(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_BackwardCorrection(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Underline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_LinearAlgebra_Matrix_Rank(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Matrix_ColumnRowPartitioned(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
