// Lean compiler output
// Module: FinitePrecisionLanczos.Run
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Matrix
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0_spec__1_spec__2___closed__0 = (const lean_object*)&lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_g_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_g_spec__0(lean_object*, lean_object*);
static lean_once_cell_t lp_Paige_FinitePrecisionLanczos_LanczosRun_g___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_g___redArg___closed__0;
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_g___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_g(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_g___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_p_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_p_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_p___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_p(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_p___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0___redArg___lam__0(lean_object* v_M_1_, lean_object* v_x_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_M_1_, v_x_2_, v_j_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0___lam__0(lean_object* v_v_5_, lean_object* v_w_6_, lean_object* v_i_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___f_10_; 
lean_inc(v_i_7_);
v___x_8_ = lean_apply_1(v_v_5_, v_i_7_);
v___x_9_ = lean_apply_1(v_w_6_, v_i_7_);
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_10_, 0, v___x_8_);
lean_closure_set(v___f_10_, 1, v___x_9_);
return v___f_10_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0_spec__1_spec__2(lean_object* v_s_12_){
_start:
{
lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___f_13_ = ((lean_object*)(lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0_spec__1_spec__2___closed__0));
v___x_14_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_15_ = l_List_foldrTR___redArg(v___f_13_, v___x_14_, v_s_12_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0_spec__1___redArg(lean_object* v_s_16_, lean_object* v_f_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lp_mathlib_Multiset_map___redArg(v_f_17_, v_s_16_);
v___x_19_ = lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0_spec__1_spec__2(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0(lean_object* v_n_20_, lean_object* v_v_21_, lean_object* v_w_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___f_23_ = lean_alloc_closure((void*)(lp_Paige_dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_23_, 0, v_v_21_);
lean_closure_set(v___f_23_, 1, v_w_22_);
v___x_24_ = l_List_finRange(v_n_20_);
v___x_25_ = lp_Paige_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0_spec__1___redArg(v___x_24_, v___f_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0___redArg(lean_object* v_n_26_, lean_object* v_M_27_, lean_object* v_v_28_, lean_object* v_x_29_){
_start:
{
lean_object* v___f_30_; lean_object* v___x_31_; 
v___f_30_ = lean_alloc_closure((void*)(lp_Paige_Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_30_, 0, v_M_27_);
lean_closure_set(v___f_30_, 1, v_x_29_);
v___x_31_ = lp_Paige_dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0(v_n_26_, v___f_30_, v_v_28_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_f___redArg(lean_object* v_n_32_, lean_object* v_L_33_, lean_object* v_j_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_H_36_; lean_object* v_v_37_; lean_object* v_00_u03b1_38_; lean_object* v_00_u03b2_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___f_51_; lean_object* v___x_52_; lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___f_55_; lean_object* v___x_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___f_59_; 
v_H_36_ = lean_ctor_get(v_L_33_, 0);
lean_inc(v_H_36_);
v_v_37_ = lean_ctor_get(v_L_33_, 1);
lean_inc_n(v_v_37_, 4);
v_00_u03b1_38_ = lean_ctor_get(v_L_33_, 5);
lean_inc(v_00_u03b1_38_);
v_00_u03b2_39_ = lean_ctor_get(v_L_33_, 6);
lean_inc_n(v_00_u03b2_39_, 2);
lean_dec_ref(v_L_33_);
lean_inc_n(v_j_34_, 3);
v___x_40_ = lean_apply_1(v_v_37_, v_j_34_);
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_sub(v_j_34_, v___x_41_);
lean_inc(v___x_42_);
v___x_43_ = lean_apply_1(v_00_u03b2_39_, v___x_42_);
v___x_44_ = lean_apply_1(v_00_u03b1_38_, v_j_34_);
v___x_45_ = lean_apply_1(v_00_u03b2_39_, v_j_34_);
v___x_46_ = lean_nat_add(v_j_34_, v___x_41_);
lean_inc_n(v_a_35_, 3);
v___x_47_ = lp_Paige_Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0___redArg(v_n_32_, v_H_36_, v___x_40_, v_a_35_);
v___x_48_ = lean_apply_2(v_v_37_, v___x_42_, v_a_35_);
v___f_49_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_49_, 0, v___x_43_);
lean_closure_set(v___f_49_, 1, v___x_48_);
v___f_50_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_50_, 0, v___f_49_);
v___f_51_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_51_, 0, v___x_47_);
lean_closure_set(v___f_51_, 1, v___f_50_);
v___x_52_ = lean_apply_2(v_v_37_, v_j_34_, v_a_35_);
v___f_53_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_53_, 0, v___x_44_);
lean_closure_set(v___f_53_, 1, v___x_52_);
v___f_54_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_54_, 0, v___f_53_);
v___f_55_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_55_, 0, v___f_51_);
lean_closure_set(v___f_55_, 1, v___f_54_);
v___x_56_ = lean_apply_2(v_v_37_, v___x_46_, v_a_35_);
v___f_57_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_57_, 0, v___x_45_);
lean_closure_set(v___f_57_, 1, v___x_56_);
v___f_58_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_58_, 0, v___f_57_);
v___f_59_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_59_, 0, v___f_55_);
lean_closure_set(v___f_59_, 1, v___f_58_);
return v___f_59_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_f(lean_object* v_n_60_, lean_object* v_k_61_, lean_object* v_L_62_, lean_object* v_j_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_f___redArg(v_n_60_, v_L_62_, v_j_63_, v_a_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_f___boxed(lean_object* v_n_66_, lean_object* v_k_67_, lean_object* v_L_68_, lean_object* v_j_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_f(v_n_66_, v_k_67_, v_L_68_, v_j_69_, v_a_70_);
lean_dec(v_k_67_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0(lean_object* v_n_72_, lean_object* v_m_73_, lean_object* v_M_74_, lean_object* v_v_75_, lean_object* v_x_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lp_Paige_Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0___redArg(v_n_72_, v_M_74_, v_v_75_, v_x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0_spec__1(lean_object* v_00_u03b9_78_, lean_object* v_s_79_, lean_object* v_f_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lp_Paige_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0_spec__0_spec__1___redArg(v_s_79_, v_f_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_g_spec__0___lam__0(lean_object* v___x_82_, lean_object* v_i_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___f_85_; 
v___x_84_ = lean_apply_1(v___x_82_, v_i_83_);
lean_inc(v___x_84_);
v___f_85_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_85_, 0, v___x_84_);
lean_closure_set(v___f_85_, 1, v___x_84_);
return v___f_85_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_g_spec__0(lean_object* v___x_86_, lean_object* v_n_87_){
_start:
{
lean_object* v___f_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___f_88_ = lean_alloc_closure((void*)(lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_g_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_88_, 0, v___x_86_);
v___x_89_ = l_List_finRange(v_n_87_);
v___x_90_ = lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_89_, v___f_88_);
return v___x_90_;
}
}
static lean_object* _init_lp_Paige_FinitePrecisionLanczos_LanczosRun_g___redArg___closed__0(void){
_start:
{
lean_object* v___x_91_; lean_object* v___f_92_; 
v___x_91_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_92_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_92_, 0, v___x_91_);
return v___f_92_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_g___redArg(lean_object* v_n_93_, lean_object* v_L_94_, lean_object* v_j_95_){
_start:
{
lean_object* v_v_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___f_99_; lean_object* v___f_100_; 
v_v_96_ = lean_ctor_get(v_L_94_, 1);
lean_inc(v_v_96_);
lean_dec_ref(v_L_94_);
v___x_97_ = lean_apply_1(v_v_96_, v_j_95_);
v___x_98_ = lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_g_spec__0(v___x_97_, v_n_93_);
v___f_99_ = lean_obj_once(&lp_Paige_FinitePrecisionLanczos_LanczosRun_g___redArg___closed__0, &lp_Paige_FinitePrecisionLanczos_LanczosRun_g___redArg___closed__0_once, _init_lp_Paige_FinitePrecisionLanczos_LanczosRun_g___redArg___closed__0);
v___f_100_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_100_, 0, v___x_98_);
lean_closure_set(v___f_100_, 1, v___f_99_);
return v___f_100_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_g(lean_object* v_n_101_, lean_object* v_k_102_, lean_object* v_L_103_, lean_object* v_j_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_g___redArg(v_n_101_, v_L_103_, v_j_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_g___boxed(lean_object* v_n_106_, lean_object* v_k_107_, lean_object* v_L_108_, lean_object* v_j_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_g(v_n_106_, v_k_107_, v_L_108_, v_j_109_);
lean_dec(v_k_107_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_p_spec__0___lam__0(lean_object* v___x_111_, lean_object* v___x_112_, lean_object* v___x_113_, lean_object* v___x_114_, lean_object* v_i_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___f_118_; lean_object* v___f_119_; 
lean_inc(v_i_115_);
v___x_116_ = lean_apply_1(v___x_111_, v_i_115_);
v___x_117_ = lean_apply_2(v___x_112_, v___x_113_, v_i_115_);
v___f_118_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_118_, 0, v___x_114_);
lean_closure_set(v___f_118_, 1, v___x_117_);
v___f_119_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_119_, 0, v___x_116_);
lean_closure_set(v___f_119_, 1, v___f_118_);
return v___f_119_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_p_spec__0(lean_object* v___x_120_, lean_object* v___x_121_, lean_object* v___x_122_, lean_object* v___x_123_, lean_object* v_n_124_){
_start:
{
lean_object* v___f_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___f_125_ = lean_alloc_closure((void*)(lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_p_spec__0___lam__0), 5, 4);
lean_closure_set(v___f_125_, 0, v___x_120_);
lean_closure_set(v___f_125_, 1, v___x_121_);
lean_closure_set(v___f_125_, 2, v___x_122_);
lean_closure_set(v___f_125_, 3, v___x_123_);
v___x_126_ = l_List_finRange(v_n_124_);
v___x_127_ = lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_126_, v___f_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_p___redArg(lean_object* v_n_128_, lean_object* v_L_129_, lean_object* v_j_130_){
_start:
{
lean_object* v_v_131_; lean_object* v_00_u03b2_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_v_131_ = lean_ctor_get(v_L_129_, 1);
lean_inc_n(v_v_131_, 2);
v_00_u03b2_132_ = lean_ctor_get(v_L_129_, 6);
lean_inc(v_00_u03b2_132_);
lean_dec_ref(v_L_129_);
lean_inc_n(v_j_130_, 2);
v___x_133_ = lean_apply_1(v_v_131_, v_j_130_);
v___x_134_ = lean_apply_1(v_00_u03b2_132_, v_j_130_);
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = lean_nat_add(v_j_130_, v___x_135_);
lean_dec(v_j_130_);
v___x_137_ = lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_p_spec__0(v___x_133_, v_v_131_, v___x_136_, v___x_134_, v_n_128_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_p(lean_object* v_n_138_, lean_object* v_k_139_, lean_object* v_L_140_, lean_object* v_j_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_p___redArg(v_n_138_, v_L_140_, v_j_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_p___boxed(lean_object* v_n_143_, lean_object* v_k_144_, lean_object* v_L_145_, lean_object* v_j_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_p(v_n_143_, v_k_144_, v_L_145_, v_j_146_);
lean_dec(v_k_144_);
return v_res_147_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Paige_FinitePrecisionLanczos_Matrix(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Paige_FinitePrecisionLanczos_Run(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Paige_FinitePrecisionLanczos_Matrix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
