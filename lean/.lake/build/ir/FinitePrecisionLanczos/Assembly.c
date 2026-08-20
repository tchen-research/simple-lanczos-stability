// Lean compiler output
// Module: FinitePrecisionLanczos.Assembly
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Bounds
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Vmat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Vmat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Vmat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Vmat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Fmat___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Fmat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Fmat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Fmat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Tmat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Tmat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Tmat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Tmat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_within___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_within___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_within(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_within___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_boundary___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_boundary___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_boundary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_boundary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Vmat___redArg(lean_object* v_L_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
lean_object* v_v_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_v_4_ = lean_ctor_get(v_L_1_, 1);
lean_inc(v_v_4_);
lean_dec_ref(v_L_1_);
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lean_nat_add(v_a_3_, v___x_5_);
v___x_7_ = lean_apply_2(v_v_4_, v___x_6_, v_a_2_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Vmat___redArg___boxed(lean_object* v_L_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_Vmat___redArg(v_L_8_, v_a_9_, v_a_10_);
lean_dec(v_a_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Vmat(lean_object* v_n_12_, lean_object* v_k_13_, lean_object* v_L_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_Vmat___redArg(v_L_14_, v_a_15_, v_a_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Vmat___boxed(lean_object* v_n_18_, lean_object* v_k_19_, lean_object* v_L_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_Vmat(v_n_18_, v_k_19_, v_L_20_, v_a_21_, v_a_22_);
lean_dec(v_a_22_);
lean_dec(v_k_19_);
lean_dec(v_n_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Fmat___redArg(lean_object* v_n_24_, lean_object* v_L_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_unsigned_to_nat(1u);
v___x_29_ = lean_nat_add(v_a_27_, v___x_28_);
v___x_30_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_f___redArg(v_n_24_, v_L_25_, v___x_29_, v_a_26_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Fmat___redArg___boxed(lean_object* v_n_31_, lean_object* v_L_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_Fmat___redArg(v_n_31_, v_L_32_, v_a_33_, v_a_34_);
lean_dec(v_a_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Fmat(lean_object* v_n_36_, lean_object* v_k_37_, lean_object* v_L_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_Fmat___redArg(v_n_36_, v_L_38_, v_a_39_, v_a_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Fmat___boxed(lean_object* v_n_42_, lean_object* v_k_43_, lean_object* v_L_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_Fmat(v_n_42_, v_k_43_, v_L_44_, v_a_45_, v_a_46_);
lean_dec(v_a_46_);
lean_dec(v_k_43_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Tmat___redArg(lean_object* v_L_48_, lean_object* v_i_49_, lean_object* v_j_50_){
_start:
{
lean_object* v___y_52_; lean_object* v___y_53_; lean_object* v___y_54_; lean_object* v___y_64_; uint8_t v___x_71_; 
v___x_71_ = lean_nat_dec_eq(v_i_49_, v_j_50_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
v___x_72_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___y_64_ = v___x_72_;
goto v___jp_63_;
}
else
{
lean_object* v_00_u03b1_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_00_u03b1_73_ = lean_ctor_get(v_L_48_, 5);
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_add(v_i_49_, v___x_74_);
lean_inc(v_00_u03b1_73_);
v___x_76_ = lean_apply_1(v_00_u03b1_73_, v___x_75_);
v___y_64_ = v___x_76_;
goto v___jp_63_;
}
v___jp_51_:
{
lean_object* v___f_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___f_55_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_55_, 0, v___y_52_);
lean_closure_set(v___f_55_, 1, v___y_54_);
v___x_56_ = lean_nat_add(v_j_50_, v___y_53_);
v___x_57_ = lean_nat_dec_eq(v___x_56_, v_i_49_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___f_59_; 
lean_dec(v___x_56_);
lean_dec_ref(v_L_48_);
v___x_58_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___f_59_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_59_, 0, v___f_55_);
lean_closure_set(v___f_59_, 1, v___x_58_);
return v___f_59_;
}
else
{
lean_object* v_00_u03b2_60_; lean_object* v___x_61_; lean_object* v___f_62_; 
v_00_u03b2_60_ = lean_ctor_get(v_L_48_, 6);
lean_inc(v_00_u03b2_60_);
lean_dec_ref(v_L_48_);
v___x_61_ = lean_apply_1(v_00_u03b2_60_, v___x_56_);
v___f_62_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_62_, 0, v___f_55_);
lean_closure_set(v___f_62_, 1, v___x_61_);
return v___f_62_;
}
}
v___jp_63_:
{
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = lean_nat_add(v_i_49_, v___x_65_);
v___x_67_ = lean_nat_dec_eq(v___x_66_, v_j_50_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; 
lean_dec(v___x_66_);
v___x_68_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___y_52_ = v___y_64_;
v___y_53_ = v___x_65_;
v___y_54_ = v___x_68_;
goto v___jp_51_;
}
else
{
lean_object* v_00_u03b2_69_; lean_object* v___x_70_; 
v_00_u03b2_69_ = lean_ctor_get(v_L_48_, 6);
lean_inc(v_00_u03b2_69_);
v___x_70_ = lean_apply_1(v_00_u03b2_69_, v___x_66_);
v___y_52_ = v___y_64_;
v___y_53_ = v___x_65_;
v___y_54_ = v___x_70_;
goto v___jp_51_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Tmat___redArg___boxed(lean_object* v_L_77_, lean_object* v_i_78_, lean_object* v_j_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_Tmat___redArg(v_L_77_, v_i_78_, v_j_79_);
lean_dec(v_j_79_);
lean_dec(v_i_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Tmat(lean_object* v_n_81_, lean_object* v_k_82_, lean_object* v_L_83_, lean_object* v_i_84_, lean_object* v_j_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_Tmat___redArg(v_L_83_, v_i_84_, v_j_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_Tmat___boxed(lean_object* v_n_87_, lean_object* v_k_88_, lean_object* v_L_89_, lean_object* v_i_90_, lean_object* v_j_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_Tmat(v_n_87_, v_k_88_, v_L_89_, v_i_90_, v_j_91_);
lean_dec(v_j_91_);
lean_dec(v_i_90_);
lean_dec(v_k_88_);
lean_dec(v_n_87_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_within___redArg(lean_object* v_k_93_, lean_object* v_L_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_v_97_; lean_object* v_00_u03b1_98_; lean_object* v_00_u03b2_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___f_108_; lean_object* v___f_109_; 
v_v_97_ = lean_ctor_get(v_L_94_, 1);
lean_inc_n(v_v_97_, 3);
v_00_u03b1_98_ = lean_ctor_get(v_L_94_, 5);
lean_inc(v_00_u03b1_98_);
v_00_u03b2_99_ = lean_ctor_get(v_L_94_, 6);
lean_inc_n(v_00_u03b2_99_, 2);
lean_dec_ref(v_L_94_);
lean_inc_n(v_a_96_, 2);
v___x_100_ = lean_apply_1(v_00_u03b2_99_, v_a_96_);
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_a_96_, v___x_101_);
lean_inc_n(v___x_102_, 2);
v___x_103_ = lean_apply_1(v_00_u03b1_98_, v___x_102_);
v___x_104_ = lean_nat_dec_lt(v___x_102_, v_k_93_);
lean_inc_n(v_a_95_, 2);
v___x_105_ = lean_apply_2(v_v_97_, v_a_96_, v_a_95_);
v___f_106_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_106_, 0, v___x_100_);
lean_closure_set(v___f_106_, 1, v___x_105_);
v___x_107_ = lean_apply_2(v_v_97_, v___x_102_, v_a_95_);
v___f_108_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_108_, 0, v___x_103_);
lean_closure_set(v___f_108_, 1, v___x_107_);
v___f_109_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_109_, 0, v___f_106_);
lean_closure_set(v___f_109_, 1, v___f_108_);
if (v___x_104_ == 0)
{
lean_object* v___x_110_; lean_object* v___f_111_; 
lean_dec(v___x_102_);
lean_dec(v_00_u03b2_99_);
lean_dec(v_v_97_);
lean_dec(v_a_96_);
lean_dec(v_a_95_);
v___x_110_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___f_111_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_111_, 0, v___f_109_);
lean_closure_set(v___f_111_, 1, v___x_110_);
return v___f_111_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___f_116_; lean_object* v___f_117_; 
v___x_112_ = lean_apply_1(v_00_u03b2_99_, v___x_102_);
v___x_113_ = lean_unsigned_to_nat(2u);
v___x_114_ = lean_nat_add(v_a_96_, v___x_113_);
lean_dec(v_a_96_);
v___x_115_ = lean_apply_2(v_v_97_, v___x_114_, v_a_95_);
v___f_116_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_116_, 0, v___x_112_);
lean_closure_set(v___f_116_, 1, v___x_115_);
v___f_117_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_117_, 0, v___f_109_);
lean_closure_set(v___f_117_, 1, v___f_116_);
return v___f_117_;
}
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_within___redArg___boxed(lean_object* v_k_118_, lean_object* v_L_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_within___redArg(v_k_118_, v_L_119_, v_a_120_, v_a_121_);
lean_dec(v_k_118_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_within(lean_object* v_n_123_, lean_object* v_k_124_, lean_object* v_L_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_within___redArg(v_k_124_, v_L_125_, v_a_126_, v_a_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_within___boxed(lean_object* v_n_129_, lean_object* v_k_130_, lean_object* v_L_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_within(v_n_129_, v_k_130_, v_L_131_, v_a_132_, v_a_133_);
lean_dec(v_k_130_);
lean_dec(v_n_129_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_boundary___redArg(lean_object* v_k_135_, lean_object* v_L_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = lean_nat_add(v_a_138_, v___x_139_);
v___x_141_ = lean_nat_dec_lt(v___x_140_, v_k_135_);
if (v___x_141_ == 0)
{
lean_object* v_v_142_; lean_object* v_00_u03b2_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___f_148_; 
v_v_142_ = lean_ctor_get(v_L_136_, 1);
lean_inc(v_v_142_);
v_00_u03b2_143_ = lean_ctor_get(v_L_136_, 6);
lean_inc(v_00_u03b2_143_);
lean_dec_ref(v_L_136_);
v___x_144_ = lean_apply_1(v_00_u03b2_143_, v___x_140_);
v___x_145_ = lean_unsigned_to_nat(2u);
v___x_146_ = lean_nat_add(v_a_138_, v___x_145_);
v___x_147_ = lean_apply_2(v_v_142_, v___x_146_, v_a_137_);
v___f_148_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_148_, 0, v___x_144_);
lean_closure_set(v___f_148_, 1, v___x_147_);
return v___f_148_;
}
else
{
lean_object* v___x_149_; 
lean_dec(v___x_140_);
lean_dec(v_a_137_);
lean_dec_ref(v_L_136_);
v___x_149_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_boundary___redArg___boxed(lean_object* v_k_150_, lean_object* v_L_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_boundary___redArg(v_k_150_, v_L_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec(v_k_150_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_boundary(lean_object* v_n_155_, lean_object* v_k_156_, lean_object* v_L_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_boundary___redArg(v_k_156_, v_L_157_, v_a_158_, v_a_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_boundary___boxed(lean_object* v_n_161_, lean_object* v_k_162_, lean_object* v_L_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_boundary(v_n_161_, v_k_162_, v_L_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec(v_k_162_);
lean_dec(v_n_161_);
return v_res_166_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Paige_FinitePrecisionLanczos_Bounds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Paige_FinitePrecisionLanczos_Assembly(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Paige_FinitePrecisionLanczos_Bounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
