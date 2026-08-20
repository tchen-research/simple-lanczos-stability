// Lean compiler output
// Module: FinitePrecisionLanczos.GreenbaumCompletion
// Imports: public import Init public meta import Init public import FinitePrecisionLanczos.MatrixCompletion
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqSum_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Function_update___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
LEAN_EXPORT uint8_t lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___lam__1___boxed(lean_object*);
static const lean_closure_object lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___closed__0 = (const lean_object*)&lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_Paige_FinitePrecisionLanczos_LanczosRun_completionFirst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_completionFirst___redArg___closed__0 = (const lean_object*)&lp_Paige_FinitePrecisionLanczos_LanczosRun_completionFirst___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_completionFirst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_completionFirst(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___lam__0(lean_object* v_k_1_, lean_object* v_d_2_, lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_5_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_5_, 0, v_k_1_);
v___x_6_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_6_, 0, v_d_2_);
v___x_7_ = l_instDecidableEqSum_decEq___redArg(v___x_5_, v___x_6_, v_a_3_, v_b_4_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___lam__0___boxed(lean_object* v_k_8_, lean_object* v_d_9_, lean_object* v_a_10_, lean_object* v_b_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___lam__0(v_k_8_, v_d_9_, v_a_10_, v_b_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___lam__1(lean_object* v_x_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___lam__1___boxed(lean_object* v_x_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___lam__1(v_x_16_);
lean_dec_ref(v_x_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0(lean_object* v_k_19_, lean_object* v_d_20_, lean_object* v_i_21_, lean_object* v_x_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___f_24_; lean_object* v___f_25_; lean_object* v___x_26_; 
v___f_24_ = lean_alloc_closure((void*)(lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___lam__0___boxed), 4, 2);
lean_closure_set(v___f_24_, 0, v_k_19_);
lean_closure_set(v___f_24_, 1, v_d_20_);
v___f_25_ = ((lean_object*)(lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___closed__0));
v___x_26_ = lp_mathlib_Function_update___redArg(v___f_24_, v___f_25_, v_i_21_, v_x_22_, v_a_23_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0___boxed(lean_object* v_k_27_, lean_object* v_d_28_, lean_object* v_i_29_, lean_object* v_x_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0(v_k_27_, v_d_28_, v_i_29_, v_x_30_, v_a_31_);
lean_dec(v_x_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_completionFirst___redArg(lean_object* v_k_35_, lean_object* v_d_36_, lean_object* v_j_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = ((lean_object*)(lp_Paige_FinitePrecisionLanczos_LanczosRun_completionFirst___redArg___closed__0));
v___x_39_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_40_ = lp_Paige_Pi_single___at___00FinitePrecisionLanczos_LanczosRun_completionFirst_spec__0(v_k_35_, v_d_36_, v___x_38_, v___x_39_, v_j_37_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_Paige_FinitePrecisionLanczos_LanczosRun_completionFirst(lean_object* v_k_41_, lean_object* v_hk_42_, lean_object* v_d_43_, lean_object* v_j_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lp_Paige_FinitePrecisionLanczos_LanczosRun_completionFirst___redArg(v_k_41_, v_d_43_, v_j_44_);
return v___x_45_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Paige_FinitePrecisionLanczos_MatrixCompletion(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Paige_FinitePrecisionLanczos_GreenbaumCompletion(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Paige_FinitePrecisionLanczos_MatrixCompletion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
