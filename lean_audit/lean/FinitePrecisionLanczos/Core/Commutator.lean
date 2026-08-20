









import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

namespace FinitePrecisionLanczos.Core

open Matrix

variable {n k : ℕ}











theorem commutator_of_governing
    (H : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin n) (Fin k) ℝ)
    (T : Matrix (Fin k) (Fin k) ℝ) (B F : Matrix (Fin n) (Fin k) ℝ)
    (hH : Hᵀ = H) (hT : Tᵀ = T)
    (hgov : H * V = V * T + B + F) :
    T * (Vᵀ * V - 1) - (Vᵀ * V - 1) * T
      = (Vᵀ * B) - (Vᵀ * B)ᵀ + (Vᵀ * F - Fᵀ * V) := by

  have key : Vᵀ * (H * V) = (Vᵀ * V) * T + Vᵀ * B + Vᵀ * F := by
    rw [hgov, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc]

  have hsymm : (Vᵀ * (H * V))ᵀ = Vᵀ * (H * V) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hH, Matrix.transpose_transpose,
      Matrix.mul_assoc]

  have key' : Vᵀ * (H * V) = T * (Vᵀ * V) + (Vᵀ * B)ᵀ + Fᵀ * V := by
    rw [← hsymm, key]
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, hT]

  have := key.symm.trans key'
  have hmul : (Vᵀ * V) * T - T * (Vᵀ * V)
      = (Vᵀ * B)ᵀ + Fᵀ * V - (Vᵀ * B) - Vᵀ * F := by
    rw [sub_eq_iff_eq_add]
    rw [show (Vᵀ * B)ᵀ + Fᵀ * V - Vᵀ * B - Vᵀ * F + T * (Vᵀ * V)
        = (T * (Vᵀ * V) + (Vᵀ * B)ᵀ + Fᵀ * V) - Vᵀ * B - Vᵀ * F by abel]
    rw [← this]
    abel
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
  rw [show T * (Vᵀ * V) - T - ((Vᵀ * V) * T - T)
      = -((Vᵀ * V) * T - T * (Vᵀ * V)) by abel]
  rw [hmul]
  abel









theorem sandwich_eq_zero
    (T R : Matrix (Fin k) (Fin k) ℝ) (hT : Tᵀ = T)
    (y : Fin k → ℝ) (θ : ℝ) (hy : T *ᵥ y = θ • y) :
    y ⬝ᵥ ((T * R - R * T) *ᵥ y) = 0 := by
  have h1 : y ⬝ᵥ ((T * R) *ᵥ y) = θ * (y ⬝ᵥ (R *ᵥ y)) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, hy]
    rw [smul_dotProduct, smul_eq_mul]
  have h2 : y ⬝ᵥ ((R * T) *ᵥ y) = θ * (y ⬝ᵥ (R *ᵥ y)) := by
    rw [← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  rw [Matrix.sub_mulVec, dotProduct_sub, h1, h2, sub_self]










theorem paige_sandwich
    (T R C N E : Matrix (Fin k) (Fin k) ℝ) (hT : Tᵀ = T)
    (y : Fin k → ℝ) (θ : ℝ) (hy : T *ᵥ y = θ • y)
    (hupper : T * R - R * T = C + N + E) :
    y ⬝ᵥ (C *ᵥ y) = -(y ⬝ᵥ (N *ᵥ y)) - y ⬝ᵥ (E *ᵥ y) := by
  have h0 := sandwich_eq_zero T R hT y θ hy
  rw [hupper] at h0
  rw [Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add] at h0
  linarith [h0]




theorem dotProduct_diagonal_mulVec (d y : Fin k → ℝ) :
    y ⬝ᵥ ((Matrix.diagonal d) *ᵥ y) = ∑ j, d j * (y j) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, Matrix.diagonal, Matrix.of_apply, dotProduct,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun j _ => by ring














theorem coeff_product {s : ℕ}
    (S : Matrix (Fin s) (Fin s) ℝ) (hS : Sᵀ = S)
    (yhat es yr : Fin s → ℝ) (θ θr βys : ℝ)
    (hrow : S *ᵥ yhat = θ • yhat - βys • es)
    (hyr : S *ᵥ yr = θr • yr) :
    (θ - θr) * (yr ⬝ᵥ yhat) = βys * (yr ⬝ᵥ es) := by
  have left : yr ⬝ᵥ (S *ᵥ yhat) = θr * (yr ⬝ᵥ yhat) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS, hyr,
      smul_dotProduct, smul_eq_mul]
  have right : yr ⬝ᵥ (S *ᵥ yhat) = θ * (yr ⬝ᵥ yhat) - βys * (yr ⬝ᵥ es) := by
    rw [hrow, dotProduct_sub, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
  have := left.symm.trans right
  linarith [this]

end FinitePrecisionLanczos.Core
