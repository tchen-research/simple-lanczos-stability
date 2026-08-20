// Lean compiler output
// Module: FinitePrecisionLanczos.Lanczos.Paige.Prefix
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Lanczos.Paige.Ritz
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
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_take___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_take(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_take___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_take___redArg(lean_object* v_L_1_){
_start:
{
lean_object* v_H_2_; lean_object* v_v_3_; lean_object* v_u_4_; lean_object* v_w_5_; lean_object* v_z_6_; lean_object* v_00_u03b1_7_; lean_object* v_00_u03b2_8_; lean_object* v_eu_9_; lean_object* v_ew_10_; lean_object* v_ez_11_; lean_object* v_e_u03b1_12_; lean_object* v_00_u0394_13_; lean_object* v_00_u03b5_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
v_H_2_ = lean_ctor_get(v_L_1_, 0);
v_v_3_ = lean_ctor_get(v_L_1_, 1);
v_u_4_ = lean_ctor_get(v_L_1_, 2);
v_w_5_ = lean_ctor_get(v_L_1_, 3);
v_z_6_ = lean_ctor_get(v_L_1_, 4);
v_00_u03b1_7_ = lean_ctor_get(v_L_1_, 5);
v_00_u03b2_8_ = lean_ctor_get(v_L_1_, 6);
v_eu_9_ = lean_ctor_get(v_L_1_, 7);
v_ew_10_ = lean_ctor_get(v_L_1_, 8);
v_ez_11_ = lean_ctor_get(v_L_1_, 9);
v_e_u03b1_12_ = lean_ctor_get(v_L_1_, 10);
v_00_u0394_13_ = lean_ctor_get(v_L_1_, 11);
v_00_u03b5_14_ = lean_ctor_get(v_L_1_, 12);
v_isSharedCheck_21_ = !lean_is_exclusive(v_L_1_);
if (v_isSharedCheck_21_ == 0)
{
v___x_16_ = v_L_1_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_00_u03b5_14_);
lean_inc(v_00_u0394_13_);
lean_inc(v_e_u03b1_12_);
lean_inc(v_ez_11_);
lean_inc(v_ew_10_);
lean_inc(v_eu_9_);
lean_inc(v_00_u03b2_8_);
lean_inc(v_00_u03b1_7_);
lean_inc(v_z_6_);
lean_inc(v_w_5_);
lean_inc(v_u_4_);
lean_inc(v_v_3_);
lean_inc(v_H_2_);
lean_dec(v_L_1_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_H_2_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_v_3_);
lean_ctor_set(v_reuseFailAlloc_20_, 2, v_u_4_);
lean_ctor_set(v_reuseFailAlloc_20_, 3, v_w_5_);
lean_ctor_set(v_reuseFailAlloc_20_, 4, v_z_6_);
lean_ctor_set(v_reuseFailAlloc_20_, 5, v_00_u03b1_7_);
lean_ctor_set(v_reuseFailAlloc_20_, 6, v_00_u03b2_8_);
lean_ctor_set(v_reuseFailAlloc_20_, 7, v_eu_9_);
lean_ctor_set(v_reuseFailAlloc_20_, 8, v_ew_10_);
lean_ctor_set(v_reuseFailAlloc_20_, 9, v_ez_11_);
lean_ctor_set(v_reuseFailAlloc_20_, 10, v_e_u03b1_12_);
lean_ctor_set(v_reuseFailAlloc_20_, 11, v_00_u0394_13_);
lean_ctor_set(v_reuseFailAlloc_20_, 12, v_00_u03b5_14_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_take(lean_object* v_n_22_, lean_object* v_k_23_, lean_object* v_L_24_, lean_object* v_t_25_, lean_object* v_ht0_26_, lean_object* v_htk_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_take___redArg(v_L_24_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_take___boxed(lean_object* v_n_29_, lean_object* v_k_30_, lean_object* v_L_31_, lean_object* v_t_32_, lean_object* v_ht0_33_, lean_object* v_htk_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_LanczosRun_take(v_n_29_, v_k_30_, v_L_31_, v_t_32_, v_ht0_33_, v_htk_34_);
lean_dec(v_t_32_);
lean_dec(v_k_30_);
lean_dec(v_n_29_);
return v_res_35_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Paige_Ritz(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Paige_Prefix(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Lanczos_Paige_Ritz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
