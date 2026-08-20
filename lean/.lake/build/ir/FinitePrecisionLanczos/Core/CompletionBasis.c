// Lean compiler output
// Module: FinitePrecisionLanczos.Core.CompletionBasis
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.Core.Tridiagonalization
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
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_sumPosition___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_sumPosition___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_sumPosition(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_sumPosition___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_familySpan(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_familySpan___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__4_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__4_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_sumPosition_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_sumPosition_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_sumPosition_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_sumPosition___redArg(lean_object* v_m_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v_val_3_; 
v_val_3_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_val_3_);
return v_val_3_;
}
else
{
lean_object* v_val_4_; lean_object* v___x_5_; 
v_val_4_ = lean_ctor_get(v_x_2_, 0);
v___x_5_ = lean_nat_add(v_m_1_, v_val_4_);
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_sumPosition___redArg___boxed(lean_object* v_m_6_, lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_sumPosition___redArg(v_m_6_, v_x_7_);
lean_dec_ref(v_x_7_);
lean_dec(v_m_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_sumPosition(lean_object* v_m_9_, lean_object* v_d_10_, lean_object* v_x_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_sumPosition___redArg(v_m_9_, v_x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_sumPosition___boxed(lean_object* v_m_13_, lean_object* v_d_14_, lean_object* v_x_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_sumPosition(v_m_13_, v_d_14_, v_x_15_);
lean_dec_ref(v_x_15_);
lean_dec(v_d_14_);
lean_dec(v_m_13_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_familySpan(lean_object* v_E_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_m_20_, lean_object* v_x_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_box(0);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos_FinitePrecisionLanczos_familySpan___boxed(lean_object* v_E_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_m_26_, lean_object* v_x_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_FinitePrecisionLanczos_FinitePrecisionLanczos_familySpan(v_E_23_, v_inst_24_, v_inst_25_, v_m_26_, v_x_27_);
lean_dec(v_x_27_);
lean_dec(v_m_26_);
lean_dec(v_inst_25_);
lean_dec_ref(v_inst_24_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__1_splitter___redArg(lean_object* v_x_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_){
_start:
{
if (lean_obj_tag(v_x_29_) == 0)
{
lean_object* v_val_32_; lean_object* v___x_33_; 
lean_dec(v_h__2_31_);
v_val_32_ = lean_ctor_get(v_x_29_, 0);
lean_inc(v_val_32_);
lean_dec_ref_known(v_x_29_, 1);
v___x_33_ = lean_apply_1(v_h__1_30_, v_val_32_);
return v___x_33_;
}
else
{
lean_object* v_val_34_; lean_object* v___x_35_; 
lean_dec(v_h__1_30_);
v_val_34_ = lean_ctor_get(v_x_29_, 0);
lean_inc(v_val_34_);
lean_dec_ref_known(v_x_29_, 1);
v___x_35_ = lean_apply_1(v_h__2_31_, v_val_34_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__1_splitter(lean_object* v_m_36_, lean_object* v_motive_37_, lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
lean_object* v_val_41_; lean_object* v___x_42_; 
lean_dec(v_h__2_40_);
v_val_41_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_val_41_);
lean_dec_ref_known(v_x_38_, 1);
v___x_42_ = lean_apply_1(v_h__1_39_, v_val_41_);
return v___x_42_;
}
else
{
lean_object* v_val_43_; lean_object* v___x_44_; 
lean_dec(v_h__1_39_);
v_val_43_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_val_43_);
lean_dec_ref_known(v_x_38_, 1);
v___x_44_ = lean_apply_1(v_h__2_40_, v_val_43_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__1_splitter___boxed(lean_object* v_m_45_, lean_object* v_motive_46_, lean_object* v_x_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__1_splitter(v_m_45_, v_motive_46_, v_x_47_, v_h__1_48_, v_h__2_49_);
lean_dec(v_m_45_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__4_splitter___redArg(lean_object* v_x_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v_val_54_; lean_object* v___x_55_; 
lean_dec(v_h__2_53_);
v_val_54_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_val_54_);
lean_dec_ref_known(v_x_51_, 1);
v___x_55_ = lean_apply_1(v_h__1_52_, v_val_54_);
return v___x_55_;
}
else
{
lean_object* v_val_56_; lean_object* v___x_57_; 
lean_dec(v_h__1_52_);
v_val_56_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_val_56_);
lean_dec_ref_known(v_x_51_, 1);
v___x_57_ = lean_apply_1(v_h__2_53_, v_val_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__4_splitter(lean_object* v_m_58_, lean_object* v_e_59_, lean_object* v_motive_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v_val_64_; lean_object* v___x_65_; 
lean_dec(v_h__2_63_);
v_val_64_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_val_64_);
lean_dec_ref_known(v_x_61_, 1);
v___x_65_ = lean_apply_1(v_h__1_62_, v_val_64_);
return v___x_65_;
}
else
{
lean_object* v_val_66_; lean_object* v___x_67_; 
lean_dec(v_h__1_62_);
v_val_66_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_val_66_);
lean_dec_ref_known(v_x_61_, 1);
v___x_67_ = lean_apply_1(v_h__2_63_, v_val_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__4_splitter___boxed(lean_object* v_m_68_, lean_object* v_e_69_, lean_object* v_motive_70_, lean_object* v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_exists__exact__tridiagonal__completion_match__1__4_splitter(v_m_68_, v_e_69_, v_motive_70_, v_x_71_, v_h__1_72_, v_h__2_73_);
lean_dec(v_e_69_);
lean_dec(v_m_68_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_sumPosition_match__1_splitter___redArg(lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_object* v_val_78_; lean_object* v___x_79_; 
lean_dec(v_h__2_77_);
v_val_78_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_val_78_);
lean_dec_ref_known(v_x_75_, 1);
v___x_79_ = lean_apply_1(v_h__1_76_, v_val_78_);
return v___x_79_;
}
else
{
lean_object* v_val_80_; lean_object* v___x_81_; 
lean_dec(v_h__1_76_);
v_val_80_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_val_80_);
lean_dec_ref_known(v_x_75_, 1);
v___x_81_ = lean_apply_1(v_h__2_77_, v_val_80_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_sumPosition_match__1_splitter(lean_object* v_m_82_, lean_object* v_d_83_, lean_object* v_motive_84_, lean_object* v_x_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v_val_88_; lean_object* v___x_89_; 
lean_dec(v_h__2_87_);
v_val_88_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_val_88_);
lean_dec_ref_known(v_x_85_, 1);
v___x_89_ = lean_apply_1(v_h__1_86_, v_val_88_);
return v___x_89_;
}
else
{
lean_object* v_val_90_; lean_object* v___x_91_; 
lean_dec(v_h__1_86_);
v_val_90_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_val_90_);
lean_dec_ref_known(v_x_85_, 1);
v___x_91_ = lean_apply_1(v_h__2_87_, v_val_90_);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_sumPosition_match__1_splitter___boxed(lean_object* v_m_92_, lean_object* v_d_93_, lean_object* v_motive_94_, lean_object* v_x_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = lp_FinitePrecisionLanczos___private_FinitePrecisionLanczos_Core_CompletionBasis_0__FinitePrecisionLanczos_sumPosition_match__1_splitter(v_m_92_, v_d_93_, v_motive_94_, v_x_95_, v_h__1_96_, v_h__2_97_);
lean_dec(v_d_93_);
lean_dec(v_m_92_);
return v_res_98_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Tridiagonalization(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_CompletionBasis(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_FinitePrecisionLanczos_FinitePrecisionLanczos_Core_Tridiagonalization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
