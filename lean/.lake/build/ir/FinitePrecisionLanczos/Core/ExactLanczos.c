// Lean compiler output
// Module: FinitePrecisionLanczos.Core.ExactLanczos
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Core.Underline
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_tridiag___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_tridiag___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_tridiag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_tridiag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_colSeq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_colSeq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_colSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_colSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_tridiag___redArg(lean_object* v_00_u03b1_1_, lean_object* v_00_u03b2_2_, lean_object* v_i_3_, lean_object* v_j_4_){
_start:
{
lean_object* v___y_6_; lean_object* v___y_7_; lean_object* v___y_8_; lean_object* v___y_17_; uint8_t v___x_23_; 
v___x_23_ = lean_nat_dec_eq(v_i_3_, v_j_4_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
lean_dec(v_00_u03b1_1_);
v___x_24_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___y_17_ = v___x_24_;
goto v___jp_16_;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_add(v_i_3_, v___x_25_);
v___x_27_ = lean_apply_1(v_00_u03b1_1_, v___x_26_);
v___y_17_ = v___x_27_;
goto v___jp_16_;
}
v___jp_5_:
{
lean_object* v___f_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v___f_9_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_9_, 0, v___y_6_);
lean_closure_set(v___f_9_, 1, v___y_8_);
v___x_10_ = lean_nat_add(v_j_4_, v___y_7_);
v___x_11_ = lean_nat_dec_eq(v___x_10_, v_i_3_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___f_13_; 
lean_dec(v___x_10_);
lean_dec(v_00_u03b2_2_);
v___x_12_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___f_13_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_13_, 0, v___f_9_);
lean_closure_set(v___f_13_, 1, v___x_12_);
return v___f_13_;
}
else
{
lean_object* v___x_14_; lean_object* v___f_15_; 
v___x_14_ = lean_apply_1(v_00_u03b2_2_, v___x_10_);
v___f_15_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_15_, 0, v___f_9_);
lean_closure_set(v___f_15_, 1, v___x_14_);
return v___f_15_;
}
}
v___jp_16_:
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = lean_nat_add(v_i_3_, v___x_18_);
v___x_20_ = lean_nat_dec_eq(v___x_19_, v_j_4_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
lean_dec(v___x_19_);
v___x_21_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___y_6_ = v___y_17_;
v___y_7_ = v___x_18_;
v___y_8_ = v___x_21_;
goto v___jp_5_;
}
else
{
lean_object* v___x_22_; 
lean_inc(v_00_u03b2_2_);
v___x_22_ = lean_apply_1(v_00_u03b2_2_, v___x_19_);
v___y_6_ = v___y_17_;
v___y_7_ = v___x_18_;
v___y_8_ = v___x_22_;
goto v___jp_5_;
}
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_tridiag___redArg___boxed(lean_object* v_00_u03b1_28_, lean_object* v_00_u03b2_29_, lean_object* v_i_30_, lean_object* v_j_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_tridiag___redArg(v_00_u03b1_28_, v_00_u03b2_29_, v_i_30_, v_j_31_);
lean_dec(v_j_31_);
lean_dec(v_i_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_tridiag(lean_object* v_k_33_, lean_object* v_00_u03b1_34_, lean_object* v_00_u03b2_35_, lean_object* v_i_36_, lean_object* v_j_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_tridiag___redArg(v_00_u03b1_34_, v_00_u03b2_35_, v_i_36_, v_j_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_tridiag___boxed(lean_object* v_k_39_, lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_, lean_object* v_i_42_, lean_object* v_j_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_tridiag(v_k_39_, v_00_u03b1_40_, v_00_u03b2_41_, v_i_42_, v_j_43_);
lean_dec(v_j_43_);
lean_dec(v_i_42_);
lean_dec(v_k_39_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_colSeq___redArg(lean_object* v_k_45_, lean_object* v_W_46_, lean_object* v_j_47_, lean_object* v_a_48_){
_start:
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_nat_dec_le(v___x_49_, v_j_47_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; 
lean_dec(v_a_48_);
lean_dec(v_W_46_);
v___x_51_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_51_;
}
else
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = lean_nat_add(v_k_45_, v___x_49_);
v___x_53_ = lean_nat_dec_le(v_j_47_, v___x_52_);
lean_dec(v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
lean_dec(v_a_48_);
lean_dec(v_W_46_);
v___x_54_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_54_;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_nat_sub(v_j_47_, v___x_49_);
v___x_56_ = lean_apply_2(v_W_46_, v_a_48_, v___x_55_);
return v___x_56_;
}
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_colSeq___redArg___boxed(lean_object* v_k_57_, lean_object* v_W_58_, lean_object* v_j_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_colSeq___redArg(v_k_57_, v_W_58_, v_j_59_, v_a_60_);
lean_dec(v_j_59_);
lean_dec(v_k_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_colSeq(lean_object* v_N_62_, lean_object* v_k_63_, lean_object* v_W_64_, lean_object* v_j_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_colSeq___redArg(v_k_63_, v_W_64_, v_j_65_, v_a_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_colSeq___boxed(lean_object* v_N_68_, lean_object* v_k_69_, lean_object* v_W_70_, lean_object* v_j_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_colSeq(v_N_68_, v_k_69_, v_W_70_, v_j_71_, v_a_72_);
lean_dec(v_j_71_);
lean_dec(v_k_69_);
return v_res_73_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Underline(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_ExactLanczos(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
