// Lean compiler output
// Module: FinitePrecisionLanczos.Core.DilationRecurrence
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Core.Dilation
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
lean_object* lp_FinitePrecisionLanczos_Pi_single___at___00FinitePrecisionLanczos_firstCoord_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_npowBinRec___at___00FinitePrecisionLanczos_triangularC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_FinitePrecisionLanczos_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_dilationStack_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_stackBlocks___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastCoord___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastCoord___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastCoord(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastCoord___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastOuter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastOuter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_powerResidual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_powerResidual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_blockDiagonal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_blockDiagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_blockDiagonal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalErrorBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalErrorBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalErrorBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalError___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastCoord___redArg(lean_object* v_k_1_, lean_object* v_j_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_sub(v_k_1_, v___x_3_);
v___x_5_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_6_ = lp_FinitePrecisionLanczos_Pi_single___at___00FinitePrecisionLanczos_firstCoord_spec__0___redArg(v___x_4_, v___x_5_, v_j_2_);
lean_dec(v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastCoord___redArg___boxed(lean_object* v_k_7_, lean_object* v_j_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastCoord___redArg(v_k_7_, v_j_8_);
lean_dec(v_k_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastCoord(lean_object* v_k_10_, lean_object* v_hk_11_, lean_object* v_j_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastCoord___redArg(v_k_10_, v_j_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastCoord___boxed(lean_object* v_k_14_, lean_object* v_hk_15_, lean_object* v_j_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastCoord(v_k_14_, v_hk_15_, v_j_16_);
lean_dec(v_k_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___lam__0(lean_object* v_w_18_, lean_object* v_v_19_, lean_object* v_x_20_, lean_object* v_y_21_){
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
static lean_object* _init_lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg(lean_object* v_w_26_, lean_object* v_v_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v___x_30_; lean_object* v_toFun_31_; lean_object* v___f_32_; lean_object* v___x_33_; 
v___x_30_ = lean_obj_once(&lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___closed__0, &lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___closed__0_once, _init_lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___closed__0);
v_toFun_31_ = lean_ctor_get(v___x_30_, 0);
v___f_32_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg___lam__0), 4, 2);
lean_closure_set(v___f_32_, 0, v_w_26_);
lean_closure_set(v___f_32_, 1, v_v_27_);
lean_inc(v_toFun_31_);
v___x_33_ = lean_apply_3(v_toFun_31_, v___f_32_, v_a_28_, v_a_29_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0(lean_object* v_m_34_, lean_object* v_n_35_, lean_object* v_w_36_, lean_object* v_v_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg(v_w_36_, v_v_37_, v_a_38_, v_a_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastOuter___redArg(lean_object* v_k_41_, lean_object* v_x_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastCoord___boxed), 3, 2);
lean_closure_set(v___x_45_, 0, v_k_41_);
lean_closure_set(v___x_45_, 1, lean_box(0));
v___x_46_ = lp_FinitePrecisionLanczos_Matrix_vecMulVec___at___00FinitePrecisionLanczos_lastOuter_spec__0___redArg(v_x_42_, v___x_45_, v_a_43_, v_a_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastOuter(lean_object* v_k_47_, lean_object* v_00_u03b9_48_, lean_object* v_hk_49_, lean_object* v_x_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_lastOuter___redArg(v_k_47_, v_x_50_, v_a_51_, v_a_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__1___lam__0(lean_object* v_k_54_, lean_object* v_n_55_, lean_object* v_K_56_, lean_object* v_a_57_, lean_object* v_L_58_, lean_object* v_a_59_, lean_object* v_i_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___f_63_; 
lean_inc(v_i_60_);
v___x_61_ = lp_FinitePrecisionLanczos_npowBinRec___at___00FinitePrecisionLanczos_triangularC_spec__0(v_k_54_, v_n_55_, v_K_56_, v_a_57_, v_i_60_);
v___x_62_ = lean_apply_2(v_L_58_, v_i_60_, v_a_59_);
v___f_63_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_63_, 0, v___x_61_);
lean_closure_set(v___f_63_, 1, v___x_62_);
return v___f_63_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__1(lean_object* v_k_64_, lean_object* v_n_65_, lean_object* v_K_66_, lean_object* v_a_67_, lean_object* v_L_68_, lean_object* v_a_69_, lean_object* v_n_70_){
_start:
{
lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___f_71_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__1___lam__0), 7, 6);
lean_closure_set(v___f_71_, 0, v_k_64_);
lean_closure_set(v___f_71_, 1, v_n_65_);
lean_closure_set(v___f_71_, 2, v_K_66_);
lean_closure_set(v___f_71_, 3, v_a_67_);
lean_closure_set(v___f_71_, 4, v_L_68_);
lean_closure_set(v___f_71_, 5, v_a_69_);
v___x_72_ = l_List_finRange(v_n_70_);
v___x_73_ = lp_FinitePrecisionLanczos_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_72_, v___f_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_powerResidual(lean_object* v_k_74_, lean_object* v_K_75_, lean_object* v_L_76_, lean_object* v_x_77_, lean_object* v_a_78_, lean_object* v_a_79_){
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
v___x_85_ = lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0(v_k_74_, v_K_75_, v_L_76_, v_n_84_, v_a_78_, v_a_79_, v_k_74_);
v___x_86_ = lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__1(v_k_74_, v_n_84_, v_K_75_, v_a_78_, v_L_76_, v_a_79_, v_k_74_);
v___f_87_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_87_, 0, v___x_85_);
lean_closure_set(v___f_87_, 1, v___x_86_);
return v___f_87_;
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0___lam__0(lean_object* v_k_88_, lean_object* v_K_89_, lean_object* v_L_90_, lean_object* v_n_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_i_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___f_97_; 
lean_inc(v_i_94_);
lean_inc(v_K_89_);
v___x_95_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_powerResidual(v_k_88_, v_K_89_, v_L_90_, v_n_91_, v_a_92_, v_i_94_);
v___x_96_ = lean_apply_2(v_K_89_, v_i_94_, v_a_93_);
v___f_97_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_97_, 0, v___x_95_);
lean_closure_set(v___f_97_, 1, v___x_96_);
return v___f_97_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0___lam__0___boxed(lean_object* v_k_98_, lean_object* v_K_99_, lean_object* v_L_100_, lean_object* v_n_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_i_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0___lam__0(v_k_98_, v_K_99_, v_L_100_, v_n_101_, v_a_102_, v_a_103_, v_i_104_);
lean_dec(v_n_101_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0(lean_object* v_k_106_, lean_object* v_K_107_, lean_object* v_L_108_, lean_object* v_n_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_n_112_){
_start:
{
lean_object* v___f_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___f_113_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_powerResidual_spec__0___lam__0___boxed), 7, 6);
lean_closure_set(v___f_113_, 0, v_k_106_);
lean_closure_set(v___f_113_, 1, v_K_107_);
lean_closure_set(v___f_113_, 2, v_L_108_);
lean_closure_set(v___f_113_, 3, v_n_109_);
lean_closure_set(v___f_113_, 4, v_a_110_);
lean_closure_set(v___f_113_, 5, v_a_111_);
v___x_114_ = l_List_finRange(v_n_112_);
v___x_115_ = lp_FinitePrecisionLanczos_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_114_, v___f_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_powerResidual___boxed(lean_object* v_k_116_, lean_object* v_K_117_, lean_object* v_L_118_, lean_object* v_x_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_powerResidual(v_k_116_, v_K_117_, v_L_118_, v_x_119_, v_a_120_, v_a_121_);
lean_dec(v_x_119_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_blockDiagonal___redArg(lean_object* v_A_123_, lean_object* v_ri_124_, lean_object* v_sj_125_){
_start:
{
lean_object* v_fst_126_; lean_object* v_snd_127_; lean_object* v_fst_128_; lean_object* v_snd_129_; uint8_t v___x_130_; 
v_fst_126_ = lean_ctor_get(v_ri_124_, 0);
lean_inc(v_fst_126_);
v_snd_127_ = lean_ctor_get(v_ri_124_, 1);
lean_inc(v_snd_127_);
lean_dec_ref(v_ri_124_);
v_fst_128_ = lean_ctor_get(v_sj_125_, 0);
lean_inc(v_fst_128_);
v_snd_129_ = lean_ctor_get(v_sj_125_, 1);
lean_inc(v_snd_129_);
lean_dec_ref(v_sj_125_);
v___x_130_ = lean_nat_dec_eq(v_fst_126_, v_fst_128_);
lean_dec(v_fst_128_);
lean_dec(v_fst_126_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
lean_dec(v_snd_129_);
lean_dec(v_snd_127_);
lean_dec(v_A_123_);
v___x_131_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_131_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = lean_apply_2(v_A_123_, v_snd_127_, v_snd_129_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_blockDiagonal(lean_object* v_n_133_, lean_object* v_p_134_, lean_object* v_A_135_, lean_object* v_ri_136_, lean_object* v_sj_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_blockDiagonal___redArg(v_A_135_, v_ri_136_, v_sj_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_blockDiagonal___boxed(lean_object* v_n_139_, lean_object* v_p_140_, lean_object* v_A_141_, lean_object* v_ri_142_, lean_object* v_sj_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_blockDiagonal(v_n_139_, v_p_140_, v_A_141_, v_ri_142_, v_sj_143_);
lean_dec(v_p_140_);
lean_dec(v_n_139_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__0___lam__0(lean_object* v_V_145_, lean_object* v_a_146_, lean_object* v_D_147_, lean_object* v_r_148_, lean_object* v_a_149_, lean_object* v___x_150_, lean_object* v_i_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___f_157_; 
lean_inc_n(v_i_151_, 2);
v___x_152_ = lean_apply_2(v_V_145_, v_a_146_, v_i_151_);
lean_inc(v_D_147_);
lean_inc(v_a_149_);
v___x_153_ = lean_apply_3(v_D_147_, v_r_148_, v_i_151_, v_a_149_);
v___x_154_ = lean_apply_3(v_D_147_, v___x_150_, v_i_151_, v_a_149_);
v___f_155_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_155_, 0, v___x_154_);
v___f_156_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_156_, 0, v___x_153_);
lean_closure_set(v___f_156_, 1, v___f_155_);
v___f_157_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_157_, 0, v___x_152_);
lean_closure_set(v___f_157_, 1, v___f_156_);
return v___f_157_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__0(lean_object* v_V_158_, lean_object* v_a_159_, lean_object* v_D_160_, lean_object* v_r_161_, lean_object* v_a_162_, lean_object* v___x_163_, lean_object* v_n_164_){
_start:
{
lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___f_165_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__0___lam__0), 7, 6);
lean_closure_set(v___f_165_, 0, v_V_158_);
lean_closure_set(v___f_165_, 1, v_a_159_);
lean_closure_set(v___f_165_, 2, v_D_160_);
lean_closure_set(v___f_165_, 3, v_r_161_);
lean_closure_set(v___f_165_, 4, v_a_162_);
lean_closure_set(v___f_165_, 5, v___x_163_);
v___x_166_ = l_List_finRange(v_n_164_);
v___x_167_ = lp_FinitePrecisionLanczos_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_166_, v___f_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalErrorBlock___redArg(lean_object* v_k_168_, lean_object* v_V_169_, lean_object* v_F_170_, lean_object* v_C_171_, lean_object* v_K_172_, lean_object* v_D_173_, lean_object* v_r_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___f_181_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_nat_add(v_r_174_, v___x_177_);
lean_inc(v_a_176_);
lean_inc(v_r_174_);
lean_inc_n(v_k_168_, 2);
lean_inc(v_a_175_);
v___x_179_ = lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_dilationStack_spec__1(v_C_171_, v_F_170_, v_a_175_, v_k_168_, v_r_174_, v_K_172_, v_a_176_, v_k_168_);
v___x_180_ = lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_physicalErrorBlock_spec__0(v_V_169_, v_a_175_, v_D_173_, v_r_174_, v_a_176_, v___x_178_, v_k_168_);
v___f_181_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_181_, 0, v___x_179_);
lean_closure_set(v___f_181_, 1, v___x_180_);
return v___f_181_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalErrorBlock(lean_object* v_n_182_, lean_object* v_k_183_, lean_object* v_V_184_, lean_object* v_F_185_, lean_object* v_C_186_, lean_object* v_K_187_, lean_object* v_D_188_, lean_object* v_r_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalErrorBlock___redArg(v_k_183_, v_V_184_, v_F_185_, v_C_186_, v_K_187_, v_D_188_, v_r_189_, v_a_190_, v_a_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalErrorBlock___boxed(lean_object* v_n_193_, lean_object* v_k_194_, lean_object* v_V_195_, lean_object* v_F_196_, lean_object* v_C_197_, lean_object* v_K_198_, lean_object* v_D_199_, lean_object* v_r_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalErrorBlock(v_n_193_, v_k_194_, v_V_195_, v_F_196_, v_C_197_, v_K_198_, v_D_199_, v_r_200_, v_a_201_, v_a_202_);
lean_dec(v_n_193_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalError___redArg___lam__0(lean_object* v_k_204_, lean_object* v_V_205_, lean_object* v_F_206_, lean_object* v_C_207_, lean_object* v_K_208_, lean_object* v_D_209_, lean_object* v_r_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalErrorBlock___redArg(v_k_204_, v_V_205_, v_F_206_, v_C_207_, v_K_208_, v_D_209_, v_r_210_, v___y_211_, v___y_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalError___redArg(lean_object* v_k_214_, lean_object* v_V_215_, lean_object* v_F_216_, lean_object* v_C_217_, lean_object* v_K_218_, lean_object* v_D_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v___f_222_; lean_object* v___x_223_; 
v___f_222_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalError___redArg___lam__0), 9, 6);
lean_closure_set(v___f_222_, 0, v_k_214_);
lean_closure_set(v___f_222_, 1, v_V_215_);
lean_closure_set(v___f_222_, 2, v_F_216_);
lean_closure_set(v___f_222_, 3, v_C_217_);
lean_closure_set(v___f_222_, 4, v_K_218_);
lean_closure_set(v___f_222_, 5, v_D_219_);
v___x_223_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_stackBlocks___redArg(v___f_222_, v_a_220_, v_a_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalError(lean_object* v_n_224_, lean_object* v_k_225_, lean_object* v_V_226_, lean_object* v_F_227_, lean_object* v_C_228_, lean_object* v_K_229_, lean_object* v_D_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalError___redArg(v_k_225_, v_V_226_, v_F_227_, v_C_228_, v_K_229_, v_D_230_, v_a_231_, v_a_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalError___boxed(lean_object* v_n_234_, lean_object* v_k_235_, lean_object* v_V_236_, lean_object* v_F_237_, lean_object* v_C_238_, lean_object* v_K_239_, lean_object* v_D_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_physicalError(v_n_234_, v_k_235_, v_V_236_, v_F_237_, v_C_238_, v_K_239_, v_D_240_, v_a_241_, v_a_242_);
lean_dec(v_n_234_);
return v_res_243_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Dilation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_DilationRecurrence(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Dilation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
