// Lean compiler output
// Module: FinitePrecisionLanczos.DilationRecurrence
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.DilationCore
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
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_firstCoord_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_Paige_npowBinRec___at___00FinitePrecisionLanczos_triangularC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalX_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_Paige_FinitePrecisionLanczos_stackBlocks___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_lastCoord___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_lastCoord___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_lastCoord(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_lastCoord___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_lastOuter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_lastOuter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_powerResidual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_powerResidual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige___private_FinitePrecisionLanczos_DilationRecurrence_0__FinitePrecisionLanczos_powerResidual_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige___private_FinitePrecisionLanczos_DilationRecurrence_0__FinitePrecisionLanczos_powerResidual_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige___private_FinitePrecisionLanczos_DilationRecurrence_0__FinitePrecisionLanczos_powerResidual_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige___private_FinitePrecisionLanczos_DilationRecurrence_0__FinitePrecisionLanczos_powerResidual_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_blockDiagonal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_blockDiagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_blockDiagonal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalErrorBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalErrorBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalErrorBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalError___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_lastCoord___redArg(lean_object* v_k_1_, lean_object* v_j_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_sub(v_k_1_, v___x_3_);
v___x_5_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_6_ = lp_Paige_Pi_single___at___00FinitePrecisionLanczos_firstCoord_spec__0___redArg(v___x_4_, v___x_5_, v_j_2_);
lean_dec(v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_lastCoord___redArg___boxed(lean_object* v_k_7_, lean_object* v_j_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_Paige_FinitePrecisionLanczos_lastCoord___redArg(v_k_7_, v_j_8_);
lean_dec(v_k_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_lastCoord(lean_object* v_k_10_, lean_object* v_hk_11_, lean_object* v_j_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_Paige_FinitePrecisionLanczos_lastCoord___redArg(v_k_10_, v_j_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_lastCoord___boxed(lean_object* v_k_14_, lean_object* v_hk_15_, lean_object* v_j_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_Paige_FinitePrecisionLanczos_lastCoord(v_k_14_, v_hk_15_, v_j_16_);
lean_dec(v_k_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___lam__0(lean_object* v_w_18_, lean_object* v_v_19_, lean_object* v_x_20_, lean_object* v_y_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___f_24_; 
v___x_22_ = lean_apply_1(v_w_18_, v_x_20_);
v___x_23_ = lean_apply_1(v_v_19_, v_y_21_);
v___f_24_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_24_, 0, v___x_22_);
lean_closure_set(v___f_24_, 1, v___x_23_);
return v___f_24_;
}
}
static lean_object* _init_lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg(lean_object* v_w_26_, lean_object* v_v_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v___x_30_; lean_object* v_toFun_31_; lean_object* v___f_32_; lean_object* v___x_33_; 
v___x_30_ = lean_obj_once(&lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___closed__0, &lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___closed__0_once, _init_lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___closed__0);
v_toFun_31_ = lean_ctor_get(v___x_30_, 0);
v___f_32_ = lean_alloc_closure((void*)(lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___lam__0), 4, 2);
lean_closure_set(v___f_32_, 0, v_w_26_);
lean_closure_set(v___f_32_, 1, v_v_27_);
lean_inc(v_toFun_31_);
v___x_33_ = lean_apply_3(v_toFun_31_, v___f_32_, v_a_28_, v_a_29_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0(lean_object* v_m_34_, lean_object* v_n_35_, lean_object* v_w_36_, lean_object* v_v_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg(v_w_36_, v_v_37_, v_a_38_, v_a_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_lastOuter___redArg(lean_object* v_k_41_, lean_object* v_x_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_alloc_closure((void*)(lp_Paige_FinitePrecisionLanczos_lastCoord___boxed), 3, 2);
lean_closure_set(v___x_45_, 0, v_k_41_);
lean_closure_set(v___x_45_, 1, lean_box(0));
v___x_46_ = lp_Paige_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg(v_x_42_, v___x_45_, v_a_43_, v_a_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_lastOuter(lean_object* v_k_47_, lean_object* v_00_u03b9_48_, lean_object* v_hk_49_, lean_object* v_x_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lp_Paige_FinitePrecisionLanczos_lastOuter___redArg(v_k_47_, v_x_50_, v_a_51_, v_a_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__1___lam__0(lean_object* v_k_54_, lean_object* v_n_55_, lean_object* v_K_56_, lean_object* v_a_57_, lean_object* v_L_58_, lean_object* v_a_59_, lean_object* v_i_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___f_63_; 
lean_inc(v_i_60_);
v___x_61_ = lp_Paige_npowBinRec___at___00FinitePrecisionLanczos_triangularC_spec__0(v_k_54_, v_n_55_, v_K_56_, v_a_57_, v_i_60_);
v___x_62_ = lean_apply_2(v_L_58_, v_i_60_, v_a_59_);
v___f_63_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_63_, 0, v___x_61_);
lean_closure_set(v___f_63_, 1, v___x_62_);
return v___f_63_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__1(lean_object* v_k_64_, lean_object* v_n_65_, lean_object* v_K_66_, lean_object* v_a_67_, lean_object* v_L_68_, lean_object* v_a_69_, lean_object* v_n_70_){
_start:
{
lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___f_71_ = lean_alloc_closure((void*)(lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__1___lam__0), 7, 6);
lean_closure_set(v___f_71_, 0, v_k_64_);
lean_closure_set(v___f_71_, 1, v_n_65_);
lean_closure_set(v___f_71_, 2, v_K_66_);
lean_closure_set(v___f_71_, 3, v_a_67_);
lean_closure_set(v___f_71_, 4, v_L_68_);
lean_closure_set(v___f_71_, 5, v_a_69_);
v___x_72_ = l_List_finRange(v_n_70_);
v___x_73_ = lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_72_, v___f_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_powerResidual(lean_object* v_k_74_, lean_object* v_K_75_, lean_object* v_L_76_, lean_object* v_x_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_zero_80_; uint8_t v_isZero_81_; 
v_zero_80_ = lean_unsigned_to_nat(0u);
v_isZero_81_ = lean_nat_dec_eq(v_x_77_, v_zero_80_);
if (v_isZero_81_ == 1)
{
lean_object* v___x_82_; 
lean_dec(v_a_79_);
lean_dec(v_a_78_);
lean_dec(v_L_76_);
lean_dec(v_K_75_);
lean_dec(v_k_74_);
v___x_82_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_82_;
}
else
{
lean_object* v_one_83_; lean_object* v_n_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___f_87_; 
v_one_83_ = lean_unsigned_to_nat(1u);
v_n_84_ = lean_nat_sub(v_x_77_, v_one_83_);
lean_inc(v_a_79_);
lean_inc(v_a_78_);
lean_inc(v_n_84_);
lean_inc(v_L_76_);
lean_inc(v_K_75_);
lean_inc_n(v_k_74_, 3);
v___x_85_ = lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0(v_k_74_, v_K_75_, v_L_76_, v_n_84_, v_a_78_, v_a_79_, v_k_74_);
v___x_86_ = lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__1(v_k_74_, v_n_84_, v_K_75_, v_a_78_, v_L_76_, v_a_79_, v_k_74_);
v___f_87_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_87_, 0, v___x_85_);
lean_closure_set(v___f_87_, 1, v___x_86_);
return v___f_87_;
}
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0___lam__0(lean_object* v_k_88_, lean_object* v_K_89_, lean_object* v_L_90_, lean_object* v_n_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_i_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___f_97_; 
lean_inc(v_i_94_);
lean_inc(v_K_89_);
v___x_95_ = lp_Paige_FinitePrecisionLanczos_powerResidual(v_k_88_, v_K_89_, v_L_90_, v_n_91_, v_a_92_, v_i_94_);
v___x_96_ = lean_apply_2(v_K_89_, v_i_94_, v_a_93_);
v___f_97_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_97_, 0, v___x_95_);
lean_closure_set(v___f_97_, 1, v___x_96_);
return v___f_97_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0___lam__0___boxed(lean_object* v_k_98_, lean_object* v_K_99_, lean_object* v_L_100_, lean_object* v_n_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_i_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0___lam__0(v_k_98_, v_K_99_, v_L_100_, v_n_101_, v_a_102_, v_a_103_, v_i_104_);
lean_dec(v_n_101_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0(lean_object* v_k_106_, lean_object* v_K_107_, lean_object* v_L_108_, lean_object* v_n_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_n_112_){
_start:
{
lean_object* v___f_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___f_113_ = lean_alloc_closure((void*)(lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0___lam__0___boxed), 7, 6);
lean_closure_set(v___f_113_, 0, v_k_106_);
lean_closure_set(v___f_113_, 1, v_K_107_);
lean_closure_set(v___f_113_, 2, v_L_108_);
lean_closure_set(v___f_113_, 3, v_n_109_);
lean_closure_set(v___f_113_, 4, v_a_110_);
lean_closure_set(v___f_113_, 5, v_a_111_);
v___x_114_ = l_List_finRange(v_n_112_);
v___x_115_ = lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_114_, v___f_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_powerResidual___boxed(lean_object* v_k_116_, lean_object* v_K_117_, lean_object* v_L_118_, lean_object* v_x_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = lp_Paige_FinitePrecisionLanczos_powerResidual(v_k_116_, v_K_117_, v_L_118_, v_x_119_, v_a_120_, v_a_121_);
lean_dec(v_x_119_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* lp_Paige___private_FinitePrecisionLanczos_DilationRecurrence_0__FinitePrecisionLanczos_powerResidual_match__1_splitter___redArg(lean_object* v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_){
_start:
{
lean_object* v_zero_126_; uint8_t v_isZero_127_; 
v_zero_126_ = lean_unsigned_to_nat(0u);
v_isZero_127_ = lean_nat_dec_eq(v_x_123_, v_zero_126_);
if (v_isZero_127_ == 1)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_h__2_125_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_apply_1(v_h__1_124_, v___x_128_);
return v___x_129_;
}
else
{
lean_object* v_one_130_; lean_object* v_n_131_; lean_object* v___x_132_; 
lean_dec(v_h__1_124_);
v_one_130_ = lean_unsigned_to_nat(1u);
v_n_131_ = lean_nat_sub(v_x_123_, v_one_130_);
v___x_132_ = lean_apply_1(v_h__2_125_, v_n_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* lp_Paige___private_FinitePrecisionLanczos_DilationRecurrence_0__FinitePrecisionLanczos_powerResidual_match__1_splitter___redArg___boxed(lean_object* v_x_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = lp_Paige___private_FinitePrecisionLanczos_DilationRecurrence_0__FinitePrecisionLanczos_powerResidual_match__1_splitter___redArg(v_x_133_, v_h__1_134_, v_h__2_135_);
lean_dec(v_x_133_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* lp_Paige___private_FinitePrecisionLanczos_DilationRecurrence_0__FinitePrecisionLanczos_powerResidual_match__1_splitter(lean_object* v_motive_137_, lean_object* v_x_138_, lean_object* v_h__1_139_, lean_object* v_h__2_140_){
_start:
{
lean_object* v_zero_141_; uint8_t v_isZero_142_; 
v_zero_141_ = lean_unsigned_to_nat(0u);
v_isZero_142_ = lean_nat_dec_eq(v_x_138_, v_zero_141_);
if (v_isZero_142_ == 1)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec(v_h__2_140_);
v___x_143_ = lean_box(0);
v___x_144_ = lean_apply_1(v_h__1_139_, v___x_143_);
return v___x_144_;
}
else
{
lean_object* v_one_145_; lean_object* v_n_146_; lean_object* v___x_147_; 
lean_dec(v_h__1_139_);
v_one_145_ = lean_unsigned_to_nat(1u);
v_n_146_ = lean_nat_sub(v_x_138_, v_one_145_);
v___x_147_ = lean_apply_1(v_h__2_140_, v_n_146_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* lp_Paige___private_FinitePrecisionLanczos_DilationRecurrence_0__FinitePrecisionLanczos_powerResidual_match__1_splitter___boxed(lean_object* v_motive_148_, lean_object* v_x_149_, lean_object* v_h__1_150_, lean_object* v_h__2_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = lp_Paige___private_FinitePrecisionLanczos_DilationRecurrence_0__FinitePrecisionLanczos_powerResidual_match__1_splitter(v_motive_148_, v_x_149_, v_h__1_150_, v_h__2_151_);
lean_dec(v_x_149_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_blockDiagonal___redArg(lean_object* v_A_153_, lean_object* v_ri_154_, lean_object* v_sj_155_){
_start:
{
lean_object* v_fst_156_; lean_object* v_snd_157_; lean_object* v_fst_158_; lean_object* v_snd_159_; uint8_t v___x_160_; 
v_fst_156_ = lean_ctor_get(v_ri_154_, 0);
lean_inc(v_fst_156_);
v_snd_157_ = lean_ctor_get(v_ri_154_, 1);
lean_inc(v_snd_157_);
lean_dec_ref(v_ri_154_);
v_fst_158_ = lean_ctor_get(v_sj_155_, 0);
lean_inc(v_fst_158_);
v_snd_159_ = lean_ctor_get(v_sj_155_, 1);
lean_inc(v_snd_159_);
lean_dec_ref(v_sj_155_);
v___x_160_ = lean_nat_dec_eq(v_fst_156_, v_fst_158_);
lean_dec(v_fst_158_);
lean_dec(v_fst_156_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
lean_dec(v_snd_159_);
lean_dec(v_snd_157_);
lean_dec(v_A_153_);
v___x_161_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_161_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = lean_apply_2(v_A_153_, v_snd_157_, v_snd_159_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_blockDiagonal(lean_object* v_n_163_, lean_object* v_k_164_, lean_object* v_A_165_, lean_object* v_ri_166_, lean_object* v_sj_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lp_Paige_FinitePrecisionLanczos_blockDiagonal___redArg(v_A_165_, v_ri_166_, v_sj_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_blockDiagonal___boxed(lean_object* v_n_169_, lean_object* v_k_170_, lean_object* v_A_171_, lean_object* v_ri_172_, lean_object* v_sj_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = lp_Paige_FinitePrecisionLanczos_blockDiagonal(v_n_169_, v_k_170_, v_A_171_, v_ri_172_, v_sj_173_);
lean_dec(v_k_170_);
lean_dec(v_n_169_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__0___lam__0(lean_object* v_E0_175_, lean_object* v_a_176_, lean_object* v_k_177_, lean_object* v_r_178_, lean_object* v_K_179_, lean_object* v_a_180_, lean_object* v_i_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___f_184_; 
lean_inc(v_i_181_);
v___x_182_ = lean_apply_2(v_E0_175_, v_a_176_, v_i_181_);
v___x_183_ = lp_Paige_npowBinRec___at___00FinitePrecisionLanczos_triangularC_spec__0(v_k_177_, v_r_178_, v_K_179_, v_i_181_, v_a_180_);
v___f_184_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_184_, 0, v___x_182_);
lean_closure_set(v___f_184_, 1, v___x_183_);
return v___f_184_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__0(lean_object* v_E0_185_, lean_object* v_a_186_, lean_object* v_k_187_, lean_object* v_r_188_, lean_object* v_K_189_, lean_object* v_a_190_, lean_object* v_n_191_){
_start:
{
lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___f_192_ = lean_alloc_closure((void*)(lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__0___lam__0), 7, 6);
lean_closure_set(v___f_192_, 0, v_E0_185_);
lean_closure_set(v___f_192_, 1, v_a_186_);
lean_closure_set(v___f_192_, 2, v_k_187_);
lean_closure_set(v___f_192_, 3, v_r_188_);
lean_closure_set(v___f_192_, 4, v_K_189_);
lean_closure_set(v___f_192_, 5, v_a_190_);
v___x_193_ = l_List_finRange(v_n_191_);
v___x_194_ = lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_193_, v___f_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__1___lam__0(lean_object* v_V_195_, lean_object* v_a_196_, lean_object* v_C_197_, lean_object* v_k_198_, lean_object* v_K_199_, lean_object* v_L_200_, lean_object* v_r_201_, lean_object* v_a_202_, lean_object* v_i_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___f_206_; 
lean_inc(v_k_198_);
lean_inc(v_i_203_);
v___x_204_ = lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalX_spec__0(v_V_195_, v_a_196_, v_C_197_, v_i_203_, v_k_198_);
v___x_205_ = lp_Paige_FinitePrecisionLanczos_powerResidual(v_k_198_, v_K_199_, v_L_200_, v_r_201_, v_i_203_, v_a_202_);
v___f_206_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_206_, 0, v___x_204_);
lean_closure_set(v___f_206_, 1, v___x_205_);
return v___f_206_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__1___lam__0___boxed(lean_object* v_V_207_, lean_object* v_a_208_, lean_object* v_C_209_, lean_object* v_k_210_, lean_object* v_K_211_, lean_object* v_L_212_, lean_object* v_r_213_, lean_object* v_a_214_, lean_object* v_i_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__1___lam__0(v_V_207_, v_a_208_, v_C_209_, v_k_210_, v_K_211_, v_L_212_, v_r_213_, v_a_214_, v_i_215_);
lean_dec(v_r_213_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__1(lean_object* v_C_217_, lean_object* v_V_218_, lean_object* v_a_219_, lean_object* v_k_220_, lean_object* v_K_221_, lean_object* v_L_222_, lean_object* v_r_223_, lean_object* v_a_224_, lean_object* v_n_225_){
_start:
{
lean_object* v___f_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___f_226_ = lean_alloc_closure((void*)(lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__1___lam__0___boxed), 9, 8);
lean_closure_set(v___f_226_, 0, v_V_218_);
lean_closure_set(v___f_226_, 1, v_a_219_);
lean_closure_set(v___f_226_, 2, v_C_217_);
lean_closure_set(v___f_226_, 3, v_k_220_);
lean_closure_set(v___f_226_, 4, v_K_221_);
lean_closure_set(v___f_226_, 5, v_L_222_);
lean_closure_set(v___f_226_, 6, v_r_223_);
lean_closure_set(v___f_226_, 7, v_a_224_);
v___x_227_ = l_List_finRange(v_n_225_);
v___x_228_ = lp_Paige_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_227_, v___f_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalErrorBlock___redArg(lean_object* v_k_229_, lean_object* v_V_230_, lean_object* v_E0_231_, lean_object* v_C_232_, lean_object* v_K_233_, lean_object* v_L_234_, lean_object* v_r_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = lean_nat_dec_eq(v_r_235_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___f_242_; 
lean_inc(v_a_237_);
lean_inc(v_K_233_);
lean_inc(v_r_235_);
lean_inc_n(v_k_229_, 3);
lean_inc(v_a_236_);
v___x_240_ = lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__0(v_E0_231_, v_a_236_, v_k_229_, v_r_235_, v_K_233_, v_a_237_, v_k_229_);
v___x_241_ = lp_Paige_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__1(v_C_232_, v_V_230_, v_a_236_, v_k_229_, v_K_233_, v_L_234_, v_r_235_, v_a_237_, v_k_229_);
v___f_242_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_242_, 0, v___x_240_);
lean_closure_set(v___f_242_, 1, v___x_241_);
return v___f_242_;
}
else
{
lean_object* v___x_243_; 
lean_dec(v_r_235_);
lean_dec(v_L_234_);
lean_dec(v_K_233_);
lean_dec(v_C_232_);
lean_dec(v_V_230_);
lean_dec(v_k_229_);
v___x_243_ = lean_apply_2(v_E0_231_, v_a_236_, v_a_237_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalErrorBlock(lean_object* v_n_244_, lean_object* v_k_245_, lean_object* v_V_246_, lean_object* v_E0_247_, lean_object* v_C_248_, lean_object* v_K_249_, lean_object* v_L_250_, lean_object* v_r_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lp_Paige_FinitePrecisionLanczos_physicalErrorBlock___redArg(v_k_245_, v_V_246_, v_E0_247_, v_C_248_, v_K_249_, v_L_250_, v_r_251_, v_a_252_, v_a_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalErrorBlock___boxed(lean_object* v_n_255_, lean_object* v_k_256_, lean_object* v_V_257_, lean_object* v_E0_258_, lean_object* v_C_259_, lean_object* v_K_260_, lean_object* v_L_261_, lean_object* v_r_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = lp_Paige_FinitePrecisionLanczos_physicalErrorBlock(v_n_255_, v_k_256_, v_V_257_, v_E0_258_, v_C_259_, v_K_260_, v_L_261_, v_r_262_, v_a_263_, v_a_264_);
lean_dec(v_n_255_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalError___redArg___lam__0(lean_object* v_k_266_, lean_object* v_V_267_, lean_object* v_E0_268_, lean_object* v_C_269_, lean_object* v_K_270_, lean_object* v_L_271_, lean_object* v_r_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lp_Paige_FinitePrecisionLanczos_physicalErrorBlock___redArg(v_k_266_, v_V_267_, v_E0_268_, v_C_269_, v_K_270_, v_L_271_, v_r_272_, v___y_273_, v___y_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalError___redArg(lean_object* v_k_276_, lean_object* v_V_277_, lean_object* v_E0_278_, lean_object* v_C_279_, lean_object* v_K_280_, lean_object* v_L_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___f_284_; lean_object* v___x_285_; 
v___f_284_ = lean_alloc_closure((void*)(lp_Paige_FinitePrecisionLanczos_physicalError___redArg___lam__0), 9, 6);
lean_closure_set(v___f_284_, 0, v_k_276_);
lean_closure_set(v___f_284_, 1, v_V_277_);
lean_closure_set(v___f_284_, 2, v_E0_278_);
lean_closure_set(v___f_284_, 3, v_C_279_);
lean_closure_set(v___f_284_, 4, v_K_280_);
lean_closure_set(v___f_284_, 5, v_L_281_);
v___x_285_ = lp_Paige_FinitePrecisionLanczos_stackBlocks___redArg(v___f_284_, v_a_282_, v_a_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalError(lean_object* v_n_286_, lean_object* v_k_287_, lean_object* v_V_288_, lean_object* v_E0_289_, lean_object* v_C_290_, lean_object* v_K_291_, lean_object* v_L_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = lp_Paige_FinitePrecisionLanczos_physicalError___redArg(v_k_287_, v_V_288_, v_E0_289_, v_C_290_, v_K_291_, v_L_292_, v_a_293_, v_a_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_physicalError___boxed(lean_object* v_n_296_, lean_object* v_k_297_, lean_object* v_V_298_, lean_object* v_E0_299_, lean_object* v_C_300_, lean_object* v_K_301_, lean_object* v_L_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = lp_Paige_FinitePrecisionLanczos_physicalError(v_n_296_, v_k_297_, v_V_298_, v_E0_299_, v_C_300_, v_K_301_, v_L_302_, v_a_303_, v_a_304_);
lean_dec(v_n_296_);
return v_res_305_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Paige_FinitePrecisionLanczos_DilationCore(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Paige_FinitePrecisionLanczos_DilationRecurrence(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Paige_FinitePrecisionLanczos_DilationCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
