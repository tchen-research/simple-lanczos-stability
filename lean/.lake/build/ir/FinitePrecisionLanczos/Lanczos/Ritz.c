// Lean compiler output
// Module: FinitePrecisionLanczos.Lanczos.Ritz
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Lanczos.Assembly public import FinitePrecisionLanczos.Core.Underline
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vmat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_Matrix_mulVec___at___00FinitePrecisionLanczos_LanczosRun_f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Tmat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_underlineT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_lastIndex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_rawBoundary___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_rawBoundary(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_rawBoundary___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_ritzVector(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vsucc___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vsucc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vsucc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vsucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_underlineTmat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vsucc___redArg(lean_object* v_L_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_v_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_v_42_ = lean_ctor_get(v_L_39_, 1);
lean_inc(v_v_42_);
lean_dec_ref(v_L_39_);
v___x_43_ = lean_unsigned_to_nat(1u);
v___x_44_ = lean_nat_add(v_a_41_, v___x_43_);
v___x_45_ = lean_apply_2(v_v_42_, v___x_44_, v_a_40_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vsucc___redArg___boxed(lean_object* v_L_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vsucc___redArg(v_L_46_, v_a_47_, v_a_48_);
lean_dec(v_a_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vsucc(lean_object* v_n_50_, lean_object* v_k_51_, lean_object* v_L_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vsucc___redArg(v_L_52_, v_a_53_, v_a_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vsucc___boxed(lean_object* v_n_56_, lean_object* v_k_57_, lean_object* v_L_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Vsucc(v_n_56_, v_k_57_, v_L_58_, v_a_59_, v_a_60_);
lean_dec(v_a_60_);
lean_dec(v_k_57_);
lean_dec(v_n_56_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_underlineTmat(lean_object* v_n_62_, lean_object* v_k_63_, lean_object* v_L_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_00_u03b2_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_00_u03b2_67_ = lean_ctor_get(v_L_64_, 6);
lean_inc(v_00_u03b2_67_);
lean_inc_n(v_k_63_, 2);
v___x_68_ = lean_alloc_closure((void*)(lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_Tmat___boxed), 5, 3);
lean_closure_set(v___x_68_, 0, v_n_62_);
lean_closure_set(v___x_68_, 1, v_k_63_);
lean_closure_set(v___x_68_, 2, v_L_64_);
v___x_69_ = lean_apply_1(v_00_u03b2_67_, v_k_63_);
v___x_70_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_underlineT(v_k_63_, v___x_68_, v___x_69_, v_a_65_, v_a_66_);
lean_dec(v___x_69_);
lean_dec(v_k_63_);
return v___x_70_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Assembly(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Underline(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Ritz(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Assembly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Underline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
