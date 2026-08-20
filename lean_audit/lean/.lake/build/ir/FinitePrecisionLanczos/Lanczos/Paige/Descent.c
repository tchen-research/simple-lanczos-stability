// Lean compiler output
// Module: FinitePrecisionLanczos.Lanczos.Paige.Descent
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Core.Descent
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
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_take___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLength___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLength___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLength(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLength___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_leadingVector___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_leadingVector(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_leadingVector___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_afterPrefix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_afterPrefix___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_afterPrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_afterPrefix___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLastBasis___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLastBasis___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLastBasis(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLastBasis___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentPrefix___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentTail___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentTail___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentTail(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentTail___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLength___redArg(lean_object* v_s_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_unsigned_to_nat(1u);
v___x_3_ = lean_nat_add(v_s_1_, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLength___redArg___boxed(lean_object* v_s_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLength___redArg(v_s_4_);
lean_dec(v_s_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLength(lean_object* v_t_6_, lean_object* v_s_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLength___redArg(v_s_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLength___boxed(lean_object* v_t_9_, lean_object* v_s_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLength(v_t_9_, v_s_10_);
lean_dec(v_s_10_);
lean_dec(v_t_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_leadingVector___redArg(lean_object* v_y_12_, lean_object* v_i_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_apply_1(v_y_12_, v_i_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_leadingVector(lean_object* v_t_15_, lean_object* v_y_16_, lean_object* v_s_17_, lean_object* v_i_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_apply_1(v_y_16_, v_i_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_leadingVector___boxed(lean_object* v_t_20_, lean_object* v_y_21_, lean_object* v_s_22_, lean_object* v_i_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_leadingVector(v_t_20_, v_y_21_, v_s_22_, v_i_23_);
lean_dec(v_s_22_);
lean_dec(v_t_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_afterPrefix___redArg(lean_object* v_y_25_, lean_object* v_s_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLength___redArg(v_s_26_);
v___x_28_ = lean_apply_1(v_y_25_, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_afterPrefix___redArg___boxed(lean_object* v_y_29_, lean_object* v_s_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_afterPrefix___redArg(v_y_29_, v_s_30_);
lean_dec(v_s_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_afterPrefix(lean_object* v_t_32_, lean_object* v_y_33_, lean_object* v_s_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_afterPrefix___redArg(v_y_33_, v_s_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_afterPrefix___boxed(lean_object* v_t_36_, lean_object* v_y_37_, lean_object* v_s_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_afterPrefix(v_t_36_, v_y_37_, v_s_38_);
lean_dec(v_s_38_);
lean_dec(v_t_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLastBasis___redArg(lean_object* v_s_40_, lean_object* v_i_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_add(v_i_41_, v___x_42_);
v___x_44_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLength___redArg(v_s_40_);
v___x_45_ = lean_nat_dec_eq(v___x_43_, v___x_44_);
lean_dec(v___x_44_);
lean_dec(v___x_43_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
v___x_46_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_46_;
}
else
{
lean_object* v___x_47_; 
v___x_47_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLastBasis___redArg___boxed(lean_object* v_s_48_, lean_object* v_i_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLastBasis___redArg(v_s_48_, v_i_49_);
lean_dec(v_i_49_);
lean_dec(v_s_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLastBasis(lean_object* v_t_51_, lean_object* v_s_52_, lean_object* v_i_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLastBasis___redArg(v_s_52_, v_i_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLastBasis___boxed(lean_object* v_t_55_, lean_object* v_s_56_, lean_object* v_i_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_prefixLastBasis(v_t_55_, v_s_56_, v_i_57_);
lean_dec(v_i_57_);
lean_dec(v_s_56_);
lean_dec(v_t_55_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentPrefix___redArg(lean_object* v_L_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_take___redArg(v_L_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentPrefix(lean_object* v_n_61_, lean_object* v_k_62_, lean_object* v_L_63_, lean_object* v_t_64_, lean_object* v_ht0_65_, lean_object* v_htk_66_, lean_object* v_s_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_take___redArg(v_L_63_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentPrefix___boxed(lean_object* v_n_69_, lean_object* v_k_70_, lean_object* v_L_71_, lean_object* v_t_72_, lean_object* v_ht0_73_, lean_object* v_htk_74_, lean_object* v_s_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentPrefix(v_n_69_, v_k_70_, v_L_71_, v_t_72_, v_ht0_73_, v_htk_74_, v_s_75_);
lean_dec(v_s_75_);
lean_dec(v_t_72_);
lean_dec(v_k_70_);
lean_dec(v_n_69_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentTail___redArg(lean_object* v_y_77_, lean_object* v_s_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_afterPrefix___redArg(v_y_77_, v_s_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentTail___redArg___boxed(lean_object* v_y_80_, lean_object* v_s_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentTail___redArg(v_y_80_, v_s_81_);
lean_dec(v_s_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentTail(lean_object* v_t_83_, lean_object* v_y_84_, lean_object* v_s_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_afterPrefix___redArg(v_y_84_, v_s_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentTail___boxed(lean_object* v_t_87_, lean_object* v_y_88_, lean_object* v_s_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_descentTail(v_t_87_, v_y_88_, v_s_89_);
lean_dec(v_s_89_);
lean_dec(v_t_87_);
return v_res_90_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Descent(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Paige_Descent(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Descent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
