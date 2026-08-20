// Lean compiler output
// Module: FinitePrecisionLanczos.ExactLanczosReproduction
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.GreenbaumModel
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqSum_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Function_update___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ExactLanczos_T___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ExactLanczos_T___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ExactLanczos_T(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ExactLanczos_T___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___lam__1___boxed(lean_object*);
static const lean_closure_object lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___closed__0 = (const lean_object*)&lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ExactLanczos_T___redArg(lean_object* v_R_1_, lean_object* v_i_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___y_5_; lean_object* v___y_6_; lean_object* v___y_7_; lean_object* v___y_17_; uint8_t v___x_24_; 
v___x_24_ = lean_nat_dec_eq(v_i_2_, v_j_3_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; 
v___x_25_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___y_17_ = v___x_25_;
goto v___jp_16_;
}
else
{
lean_object* v_00_u03b1_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v_00_u03b1_26_ = lean_ctor_get(v_R_1_, 1);
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_add(v_i_2_, v___x_27_);
lean_inc(v_00_u03b1_26_);
v___x_29_ = lean_apply_1(v_00_u03b1_26_, v___x_28_);
v___y_17_ = v___x_29_;
goto v___jp_16_;
}
v___jp_4_:
{
lean_object* v___f_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v___f_8_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_8_, 0, v___y_6_);
lean_closure_set(v___f_8_, 1, v___y_7_);
v___x_9_ = lean_nat_add(v_j_3_, v___y_5_);
v___x_10_ = lean_nat_dec_eq(v___x_9_, v_i_2_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; lean_object* v___f_12_; 
lean_dec(v___x_9_);
lean_dec_ref(v_R_1_);
v___x_11_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___f_12_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_12_, 0, v___f_8_);
lean_closure_set(v___f_12_, 1, v___x_11_);
return v___f_12_;
}
else
{
lean_object* v_00_u03b2_13_; lean_object* v___x_14_; lean_object* v___f_15_; 
v_00_u03b2_13_ = lean_ctor_get(v_R_1_, 2);
lean_inc(v_00_u03b2_13_);
lean_dec_ref(v_R_1_);
v___x_14_ = lean_apply_1(v_00_u03b2_13_, v___x_9_);
v___f_15_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_15_, 0, v___f_8_);
lean_closure_set(v___f_15_, 1, v___x_14_);
return v___f_15_;
}
}
v___jp_16_:
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = lean_nat_add(v_i_2_, v___x_18_);
v___x_20_ = lean_nat_dec_eq(v___x_19_, v_j_3_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
lean_dec(v___x_19_);
v___x_21_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___y_5_ = v___x_18_;
v___y_6_ = v___y_17_;
v___y_7_ = v___x_21_;
goto v___jp_4_;
}
else
{
lean_object* v_00_u03b2_22_; lean_object* v___x_23_; 
v_00_u03b2_22_ = lean_ctor_get(v_R_1_, 2);
lean_inc(v_00_u03b2_22_);
v___x_23_ = lean_apply_1(v_00_u03b2_22_, v___x_19_);
v___y_5_ = v___x_18_;
v___y_6_ = v___y_17_;
v___y_7_ = v___x_23_;
goto v___jp_4_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ExactLanczos_T___redArg___boxed(lean_object* v_R_30_, lean_object* v_i_31_, lean_object* v_j_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_Paige_FinitePrecisionLanczos_ExactLanczos_T___redArg(v_R_30_, v_i_31_, v_j_32_);
lean_dec(v_j_32_);
lean_dec(v_i_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ExactLanczos_T(lean_object* v_N_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_S_37_, lean_object* v_q_38_, lean_object* v_steps_39_, lean_object* v_R_40_, lean_object* v_i_41_, lean_object* v_j_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_Paige_FinitePrecisionLanczos_ExactLanczos_T___redArg(v_R_40_, v_i_41_, v_j_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_ExactLanczos_T___boxed(lean_object* v_N_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_S_47_, lean_object* v_q_48_, lean_object* v_steps_49_, lean_object* v_R_50_, lean_object* v_i_51_, lean_object* v_j_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_Paige_FinitePrecisionLanczos_ExactLanczos_T(v_N_44_, v_inst_45_, v_inst_46_, v_S_47_, v_q_48_, v_steps_49_, v_R_50_, v_i_51_, v_j_52_);
lean_dec(v_j_52_);
lean_dec(v_i_51_);
lean_dec(v_steps_49_);
lean_dec(v_q_48_);
lean_dec(v_S_47_);
lean_dec_ref(v_inst_46_);
lean_dec(v_inst_45_);
return v_res_53_;
}
}
LEAN_EXPORT uint8_t lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___lam__0(lean_object* v_M_54_, lean_object* v_k_55_, lean_object* v_a_56_, lean_object* v_b_57_){
_start:
{
lean_object* v_d_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v_d_58_ = lean_ctor_get(v_M_54_, 0);
lean_inc(v_d_58_);
lean_dec_ref(v_M_54_);
v___x_59_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_59_, 0, v_k_55_);
v___x_60_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_60_, 0, v_d_58_);
v___x_61_ = l_instDecidableEqSum_decEq___redArg(v___x_59_, v___x_60_, v_a_56_, v_b_57_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___lam__0___boxed(lean_object* v_M_62_, lean_object* v_k_63_, lean_object* v_a_64_, lean_object* v_b_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___lam__0(v_M_62_, v_k_63_, v_a_64_, v_b_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___lam__1(lean_object* v_x_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___lam__1___boxed(lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___lam__1(v_x_70_);
lean_dec_ref(v_x_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0(lean_object* v_k_73_, lean_object* v_M_74_, lean_object* v_i_75_, lean_object* v_x_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___f_78_; lean_object* v___f_79_; lean_object* v___x_80_; 
v___f_78_ = lean_alloc_closure((void*)(lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___lam__0___boxed), 4, 2);
lean_closure_set(v___f_78_, 0, v_M_74_);
lean_closure_set(v___f_78_, 1, v_k_73_);
v___f_79_ = ((lean_object*)(lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___closed__0));
v___x_80_ = lp_mathlib_Function_update___redArg(v___f_78_, v___f_79_, v_i_75_, v_x_76_, v_a_77_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0___boxed(lean_object* v_k_81_, lean_object* v_M_82_, lean_object* v_i_83_, lean_object* v_x_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0(v_k_81_, v_M_82_, v_i_83_, v_x_84_, v_a_85_);
lean_dec(v_x_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis___redArg(lean_object* v_k_87_, lean_object* v_M_88_, lean_object* v_j_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = lean_nat_dec_le(v___x_91_, v_j_89_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_dec_ref(v_a_90_);
lean_dec_ref(v_M_88_);
lean_dec(v_k_87_);
v___x_93_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_93_;
}
else
{
uint8_t v___x_94_; 
v___x_94_ = lean_nat_dec_le(v_j_89_, v_k_87_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
lean_dec_ref(v_a_90_);
lean_dec_ref(v_M_88_);
lean_dec(v_k_87_);
v___x_95_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_95_;
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = lean_nat_sub(v_j_89_, v___x_91_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
v___x_98_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_99_ = lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis_spec__0(v_k_87_, v_M_88_, v___x_97_, v___x_98_, v_a_90_);
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis___redArg___boxed(lean_object* v_k_100_, lean_object* v_M_101_, lean_object* v_j_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis___redArg(v_k_100_, v_M_101_, v_j_102_, v_a_103_);
lean_dec(v_j_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis(lean_object* v_n_105_, lean_object* v_k_106_, lean_object* v_L_107_, lean_object* v_M_108_, lean_object* v_j_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis___redArg(v_k_106_, v_M_108_, v_j_109_, v_a_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis___boxed(lean_object* v_n_112_, lean_object* v_k_113_, lean_object* v_L_114_, lean_object* v_M_115_, lean_object* v_j_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_GreenbaumModel_lanczosBasis(v_n_112_, v_k_113_, v_L_114_, v_M_115_, v_j_116_, v_a_117_);
lean_dec(v_j_116_);
lean_dec_ref(v_L_114_);
lean_dec(v_n_112_);
return v_res_118_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Paige_FinitePrecisionLanczos_GreenbaumModel(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Paige_FinitePrecisionLanczos_ExactLanczosReproduction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Paige_FinitePrecisionLanczos_GreenbaumModel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
