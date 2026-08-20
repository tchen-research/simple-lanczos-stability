// Lean compiler output
// Module: FinitePrecisionLanczos.Lanczos.Paige.Loss
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Lanczos.Paige.Commutator
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_upG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_FinitePrecisionLanczos_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_upQ(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vmat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_npowRec___at___00NNReal_instSemiring_spec__1(lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_p___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_rawBoundary___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_rawBoundary(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_rawBoundary___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_ritzVector(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_eta_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_eta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_eta_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_eta(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_paigeSum___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_paigeSum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex___redArg(lean_object* v_k_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_unsigned_to_nat(1u);
v___x_3_ = lean_nat_sub(v_k_1_, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex___redArg___boxed(lean_object* v_k_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex___redArg(v_k_4_);
lean_dec(v_k_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex(lean_object* v_k_6_, lean_object* v_hk_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex___redArg(v_k_6_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex___boxed(lean_object* v_k_9_, lean_object* v_hk_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex(v_k_9_, v_hk_10_);
lean_dec(v_k_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_rawBoundary___redArg(lean_object* v_k_12_, lean_object* v_L_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_v_15_; lean_object* v_00_u03b2_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___f_21_; 
v_v_15_ = lean_ctor_get(v_L_13_, 1);
lean_inc(v_v_15_);
v_00_u03b2_16_ = lean_ctor_get(v_L_13_, 6);
lean_inc(v_00_u03b2_16_);
lean_dec_ref(v_L_13_);
lean_inc(v_k_12_);
v___x_17_ = lean_apply_1(v_00_u03b2_16_, v_k_12_);
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = lean_nat_add(v_k_12_, v___x_18_);
lean_dec(v_k_12_);
v___x_20_ = lean_apply_2(v_v_15_, v___x_19_, v_a_14_);
v___f_21_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_21_, 0, v___x_17_);
lean_closure_set(v___f_21_, 1, v___x_20_);
return v___f_21_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_rawBoundary(lean_object* v_n_22_, lean_object* v_k_23_, lean_object* v_L_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_rawBoundary___redArg(v_k_23_, v_L_24_, v_a_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_rawBoundary___boxed(lean_object* v_n_27_, lean_object* v_k_28_, lean_object* v_L_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_rawBoundary(v_n_27_, v_k_28_, v_L_29_, v_a_30_);
lean_dec(v_n_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_ritzVector(lean_object* v_n_32_, lean_object* v_k_33_, lean_object* v_L_34_, lean_object* v_y_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
lean_inc(v_k_33_);
v___x_37_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vmat___boxed), 5, 3);
lean_closure_set(v___x_37_, 0, v_n_32_);
lean_closure_set(v___x_37_, 1, v_k_33_);
lean_closure_set(v___x_37_, 2, v_L_34_);
v___x_38_ = lp_FinitePrecisionLanczos_Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0___redArg(v_k_33_, v___x_37_, v_y_35_, v_a_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_eta_spec__0___lam__0(lean_object* v_y_39_, lean_object* v_k_40_, lean_object* v___x_41_, lean_object* v_i_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___f_45_; 
lean_inc(v_y_39_);
lean_inc(v_i_42_);
v___x_43_ = lean_apply_1(v_y_39_, v_i_42_);
v___x_44_ = lp_FinitePrecisionLanczos_Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0___redArg(v_k_40_, v___x_41_, v_y_39_, v_i_42_);
v___f_45_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_45_, 0, v___x_43_);
lean_closure_set(v___f_45_, 1, v___x_44_);
return v___f_45_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_eta_spec__0(lean_object* v_y_46_, lean_object* v_k_47_, lean_object* v_n_48_, lean_object* v_L_49_, lean_object* v_n_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___f_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
lean_inc(v_k_47_);
v___x_51_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_upG), 5, 3);
lean_closure_set(v___x_51_, 0, v_n_48_);
lean_closure_set(v___x_51_, 1, v_k_47_);
lean_closure_set(v___x_51_, 2, v_L_49_);
v___f_52_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_eta_spec__0___lam__0), 4, 3);
lean_closure_set(v___f_52_, 0, v_y_46_);
lean_closure_set(v___f_52_, 1, v_k_47_);
lean_closure_set(v___f_52_, 2, v___x_51_);
v___x_53_ = l_List_finRange(v_n_50_);
v___x_54_ = lp_FinitePrecisionLanczos_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_53_, v___f_52_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_eta_spec__1(lean_object* v_y_55_, lean_object* v_k_56_, lean_object* v_n_57_, lean_object* v_L_58_, lean_object* v_n_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
lean_inc(v_k_56_);
v___x_60_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_upQ), 5, 3);
lean_closure_set(v___x_60_, 0, v_n_57_);
lean_closure_set(v___x_60_, 1, v_k_56_);
lean_closure_set(v___x_60_, 2, v_L_58_);
v___f_61_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_eta_spec__0___lam__0), 4, 3);
lean_closure_set(v___f_61_, 0, v_y_55_);
lean_closure_set(v___f_61_, 1, v_k_56_);
lean_closure_set(v___f_61_, 2, v___x_60_);
v___x_62_ = l_List_finRange(v_n_59_);
v___x_63_ = lp_FinitePrecisionLanczos_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_62_, v___f_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_eta(lean_object* v_n_64_, lean_object* v_k_65_, lean_object* v_L_66_, lean_object* v_y_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___f_69_; lean_object* v___x_70_; lean_object* v___f_71_; 
lean_inc_ref(v_L_66_);
lean_inc(v_n_64_);
lean_inc_n(v_k_65_, 3);
lean_inc(v_y_67_);
v___x_68_ = lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_eta_spec__0(v_y_67_, v_k_65_, v_n_64_, v_L_66_, v_k_65_);
v___f_69_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_69_, 0, v___x_68_);
v___x_70_ = lp_FinitePrecisionLanczos_dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0___at___00FinitePrecisionLanczos_LanczosRun_eta_spec__1(v_y_67_, v_k_65_, v_n_64_, v_L_66_, v_k_65_);
v___f_71_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_71_, 0, v___f_69_);
lean_closure_set(v___f_71_, 1, v___x_70_);
return v___f_71_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_paigeSum___lam__0(lean_object* v_y_72_, lean_object* v_n_73_, lean_object* v_L_74_, lean_object* v_j_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___f_83_; lean_object* v___f_84_; lean_object* v___f_85_; 
lean_inc(v_j_75_);
v___x_76_ = lean_apply_1(v_y_72_, v_j_75_);
v___x_77_ = lean_unsigned_to_nat(2u);
v___x_78_ = lp_mathlib_npowRec___at___00NNReal_instSemiring_spec__1(v___x_77_, v___x_76_);
v___x_79_ = lean_unsigned_to_nat(1u);
v___x_80_ = lean_nat_add(v_j_75_, v___x_79_);
lean_inc_ref(v_L_74_);
lean_inc(v_n_73_);
v___x_81_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_p___redArg(v_n_73_, v_L_74_, v___x_80_);
v___x_82_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_p___redArg(v_n_73_, v_L_74_, v_j_75_);
v___f_83_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_83_, 0, v___x_82_);
v___f_84_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_84_, 0, v___x_81_);
lean_closure_set(v___f_84_, 1, v___f_83_);
v___f_85_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_85_, 0, v___x_78_);
lean_closure_set(v___f_85_, 1, v___f_84_);
return v___f_85_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_paigeSum(lean_object* v_n_86_, lean_object* v_k_87_, lean_object* v_L_88_, lean_object* v_y_89_){
_start:
{
lean_object* v___f_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___f_90_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_paigeSum___lam__0), 4, 3);
lean_closure_set(v___f_90_, 0, v_y_89_);
lean_closure_set(v___f_90_, 1, v_n_86_);
lean_closure_set(v___f_90_, 2, v_L_88_);
v___x_91_ = l_List_finRange(v_k_87_);
v___x_92_ = lp_FinitePrecisionLanczos_Finset_sum___at___00dotProduct___at___00FinitePrecisionLanczos_vdot_spec__0_spec__0___redArg(v___x_91_, v___f_90_);
return v___x_92_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Paige_Commutator(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Paige_Loss(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Paige_Commutator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
