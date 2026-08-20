// Lean compiler output
// Module: Paige.Run
// Imports: public import Init public meta import Init public import Mathlib.Data.Matrix.Mul public import Mathlib.Tactic
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Paige_LanczosRun_f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Paige_LanczosRun_f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Paige_LanczosRun_f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Paige_LanczosRun_g_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Paige_LanczosRun_g_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Paige_LanczosRun_g_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Paige_LanczosRun_g_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00Paige_LanczosRun_g_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00Paige_LanczosRun_g_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00Paige_LanczosRun_g_spec__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_Paige_Paige_LanczosRun_g___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Paige_Paige_LanczosRun_g___closed__0;
LEAN_EXPORT lean_object* lp_Paige_Paige_LanczosRun_g(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00Paige_LanczosRun_g_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Paige_LanczosRun_p(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Paige_LanczosRun_00_u03be(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Paige_LanczosRun_f___redArg(lean_object* v_L_1_, lean_object* v_j_2_, lean_object* v_a_3_){
_start:
{
lean_object* v_eu_4_; lean_object* v_ew_5_; lean_object* v_ez_6_; lean_object* v_00_u0394_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___f_12_; lean_object* v___x_13_; lean_object* v___f_14_; lean_object* v___f_15_; 
v_eu_4_ = lean_ctor_get(v_L_1_, 7);
lean_inc(v_eu_4_);
v_ew_5_ = lean_ctor_get(v_L_1_, 8);
lean_inc(v_ew_5_);
v_ez_6_ = lean_ctor_get(v_L_1_, 9);
lean_inc(v_ez_6_);
v_00_u0394_7_ = lean_ctor_get(v_L_1_, 11);
lean_inc(v_00_u0394_7_);
lean_dec_ref(v_L_1_);
lean_inc_n(v_a_3_, 3);
lean_inc_n(v_j_2_, 3);
v___x_8_ = lean_apply_2(v_eu_4_, v_j_2_, v_a_3_);
v___x_9_ = lean_apply_2(v_ew_5_, v_j_2_, v_a_3_);
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_10_, 0, v___x_8_);
lean_closure_set(v___f_10_, 1, v___x_9_);
v___x_11_ = lean_apply_2(v_ez_6_, v_j_2_, v_a_3_);
v___f_12_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_12_, 0, v___f_10_);
lean_closure_set(v___f_12_, 1, v___x_11_);
v___x_13_ = lean_apply_2(v_00_u0394_7_, v_j_2_, v_a_3_);
v___f_14_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_14_, 0, v___f_12_);
lean_closure_set(v___f_14_, 1, v___x_13_);
v___f_15_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_15_, 0, v___f_14_);
return v___f_15_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Paige_LanczosRun_f(lean_object* v_n_16_, lean_object* v_L_17_, lean_object* v_j_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_Paige_Paige_LanczosRun_f___redArg(v_L_17_, v_j_18_, v_a_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Paige_LanczosRun_f___boxed(lean_object* v_n_21_, lean_object* v_L_22_, lean_object* v_j_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_Paige_Paige_LanczosRun_f(v_n_21_, v_L_22_, v_j_23_, v_a_24_);
lean_dec(v_n_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Paige_LanczosRun_g_spec__0_spec__0_spec__1(lean_object* v_s_27_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___f_28_ = ((lean_object*)(lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Paige_LanczosRun_g_spec__0_spec__0_spec__1___closed__0));
v___x_29_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_30_ = l_List_foldrTR___redArg(v___f_28_, v___x_29_, v_s_27_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00Paige_LanczosRun_g_spec__0_spec__0___redArg(lean_object* v_s_31_, lean_object* v_f_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lp_mathlib_Multiset_map___redArg(v_f_32_, v_s_31_);
v___x_34_ = lp_Paige_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Paige_LanczosRun_g_spec__0_spec__0_spec__1(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00Paige_LanczosRun_g_spec__0___lam__0(lean_object* v_v_35_, lean_object* v_w_36_, lean_object* v_i_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___f_40_; 
lean_inc(v_i_37_);
v___x_38_ = lean_apply_1(v_v_35_, v_i_37_);
v___x_39_ = lean_apply_1(v_w_36_, v_i_37_);
v___f_40_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_40_, 0, v___x_38_);
lean_closure_set(v___f_40_, 1, v___x_39_);
return v___f_40_;
}
}
LEAN_EXPORT lean_object* lp_Paige_dotProduct___at___00Paige_LanczosRun_g_spec__0(lean_object* v_n_41_, lean_object* v_v_42_, lean_object* v_w_43_){
_start:
{
lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___f_44_ = lean_alloc_closure((void*)(lp_Paige_dotProduct___at___00Paige_LanczosRun_g_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_44_, 0, v_v_42_);
lean_closure_set(v___f_44_, 1, v_w_43_);
v___x_45_ = l_List_finRange(v_n_41_);
v___x_46_ = lp_Paige_Finset_sum___at___00dotProduct___at___00Paige_LanczosRun_g_spec__0_spec__0___redArg(v___x_45_, v___f_44_);
return v___x_46_;
}
}
static lean_object* _init_lp_Paige_Paige_LanczosRun_g___closed__0(void){
_start:
{
lean_object* v___x_47_; lean_object* v___f_48_; 
v___x_47_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___f_48_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_48_, 0, v___x_47_);
return v___f_48_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Paige_LanczosRun_g(lean_object* v_n_49_, lean_object* v_L_50_, lean_object* v_j_51_){
_start:
{
lean_object* v_v_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___f_55_; lean_object* v___f_56_; 
v_v_52_ = lean_ctor_get(v_L_50_, 1);
lean_inc(v_v_52_);
lean_dec_ref(v_L_50_);
v___x_53_ = lean_apply_1(v_v_52_, v_j_51_);
lean_inc(v___x_53_);
v___x_54_ = lp_Paige_dotProduct___at___00Paige_LanczosRun_g_spec__0(v_n_49_, v___x_53_, v___x_53_);
v___f_55_ = lean_obj_once(&lp_Paige_Paige_LanczosRun_g___closed__0, &lp_Paige_Paige_LanczosRun_g___closed__0_once, _init_lp_Paige_Paige_LanczosRun_g___closed__0);
v___f_56_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_56_, 0, v___x_54_);
lean_closure_set(v___f_56_, 1, v___f_55_);
return v___f_56_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Finset_sum___at___00dotProduct___at___00Paige_LanczosRun_g_spec__0_spec__0(lean_object* v_00_u03b9_57_, lean_object* v_s_58_, lean_object* v_f_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_Paige_Finset_sum___at___00dotProduct___at___00Paige_LanczosRun_g_spec__0_spec__0___redArg(v_s_58_, v_f_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Paige_LanczosRun_p(lean_object* v_n_61_, lean_object* v_L_62_, lean_object* v_j_63_){
_start:
{
lean_object* v_v_64_; lean_object* v_00_u03b2_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___f_72_; 
v_v_64_ = lean_ctor_get(v_L_62_, 1);
lean_inc_n(v_v_64_, 2);
v_00_u03b2_65_ = lean_ctor_get(v_L_62_, 6);
lean_inc(v_00_u03b2_65_);
lean_dec_ref(v_L_62_);
lean_inc_n(v_j_63_, 2);
v___x_66_ = lean_apply_1(v_00_u03b2_65_, v_j_63_);
v___x_67_ = lean_apply_1(v_v_64_, v_j_63_);
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_add(v_j_63_, v___x_68_);
lean_dec(v_j_63_);
v___x_70_ = lean_apply_1(v_v_64_, v___x_69_);
v___x_71_ = lp_Paige_dotProduct___at___00Paige_LanczosRun_g_spec__0(v_n_61_, v___x_67_, v___x_70_);
v___f_72_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_72_, 0, v___x_66_);
lean_closure_set(v___f_72_, 1, v___x_71_);
return v___f_72_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Paige_LanczosRun_00_u03be(lean_object* v_n_73_, lean_object* v_L_74_, lean_object* v_j_75_){
_start:
{
lean_object* v_v_76_; lean_object* v_00_u03b2_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___f_88_; 
v_v_76_ = lean_ctor_get(v_L_74_, 1);
lean_inc_n(v_v_76_, 2);
v_00_u03b2_77_ = lean_ctor_get(v_L_74_, 6);
lean_inc_n(v_00_u03b2_77_, 2);
lean_dec_ref(v_L_74_);
lean_inc_n(v_j_75_, 2);
v___x_78_ = lean_apply_1(v_00_u03b2_77_, v_j_75_);
v___x_79_ = lean_unsigned_to_nat(1u);
v___x_80_ = lean_nat_add(v_j_75_, v___x_79_);
v___x_81_ = lean_apply_1(v_00_u03b2_77_, v___x_80_);
v___f_82_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_82_, 0, v___x_78_);
lean_closure_set(v___f_82_, 1, v___x_81_);
v___x_83_ = lean_apply_1(v_v_76_, v_j_75_);
v___x_84_ = lean_unsigned_to_nat(2u);
v___x_85_ = lean_nat_add(v_j_75_, v___x_84_);
lean_dec(v_j_75_);
v___x_86_ = lean_apply_1(v_v_76_, v___x_85_);
v___x_87_ = lp_Paige_dotProduct___at___00Paige_LanczosRun_g_spec__0(v_n_73_, v___x_83_, v___x_86_);
v___f_88_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_88_, 0, v___f_82_);
lean_closure_set(v___f_88_, 1, v___x_87_);
return v___f_88_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Matrix_Mul(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Paige_Paige_Run(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Matrix_Mul(builtin);
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
