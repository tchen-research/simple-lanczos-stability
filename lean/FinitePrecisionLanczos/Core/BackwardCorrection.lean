import FinitePrecisionLanczos.Core.Underline
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}

def backwardCorrected (A : Matrix I I ℝ) (X E : Matrix I (Fin k) ℝ) (T : Mat k k) :
    Matrix I I ℝ :=
  A - E * Xᵀ - X * Eᵀ + X * (Xᵀ * A * X - T) * Xᵀ

omit [DecidableEq I] in
theorem backwardCorrected_transpose (A : Matrix I I ℝ) (X E : Matrix I (Fin k) ℝ)
    (T : Mat k k) (hA : Aᵀ = A) (hT : Tᵀ = T) :
    (backwardCorrected A X E T)ᵀ = backwardCorrected A X E T := by
  simp only [backwardCorrected, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_mul, Matrix.transpose_transpose, hA, hT, Matrix.mul_assoc]
  abel

omit [Fintype I] [DecidableEq I] in
lemma leadCols_eq_mul_embedJ (W : Matrix I (Fin (k + 1)) ℝ) :
    leadCols W = W * embedJ := by
  rw [embedJ, mul_padRow, Matrix.mul_one]

omit [DecidableEq I] in
theorem leadCols_transpose_mul_underlineT (W : Matrix I (Fin (k + 1)) ℝ)
    (hW : Wᵀ * W = 1) (T : Mat k k) (β : ℝ) :
    (leadCols W)ᵀ * (W * underlineT T β) = T := by
  rw [leadCols_eq_mul_embedJ, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Wᵀ, hW, Matrix.one_mul, embedJ_transpose_mul]
  ext i j
  simp [topRows]

omit [DecidableEq I] in
theorem projected_error_eq (A : Matrix I I ℝ) (W : Matrix I (Fin (k + 1)) ℝ)
    (E : Matrix I (Fin k) ℝ) (T : Mat k k) (β : ℝ) (hW : Wᵀ * W = 1)
    (hrec : A * leadCols W = W * underlineT T β + E) :
    (leadCols W)ᵀ * E = (leadCols W)ᵀ * A * leadCols W - T := by
  rw [Matrix.mul_assoc, hrec, Matrix.mul_add,
    leadCols_transpose_mul_underlineT W hW]
  abel

omit [DecidableEq I] in
theorem projected_error_transpose (A : Matrix I I ℝ) (X E : Matrix I (Fin k) ℝ)
    (T : Mat k k) (hA : Aᵀ = A) (hT : Tᵀ = T)
    (hXE : Xᵀ * E = Xᵀ * A * X - T) :
    Eᵀ * X = Xᵀ * E := by
  have h := congrArg Matrix.transpose hXE
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_sub,
    hA, hT, Matrix.mul_assoc] at h
  rw [h, hXE, Matrix.mul_assoc]

theorem backwardDelta_projector (A : Matrix I I ℝ) (X E : Matrix I (Fin k) ℝ)
    (T : Mat k k) (hA : Aᵀ = A) (hT : Tᵀ = T)
    (hXE : Xᵀ * E = Xᵀ * A * X - T) :
    backwardCorrected A X E T - A = -(E * Xᵀ) - X * Eᵀ * (1 - X * Xᵀ) := by
  have hEX := projected_error_transpose A X E T hA hT hXE
  rw [backwardCorrected, ← hXE, ← hEX]
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  abel

theorem norm_one_sub_mul_transpose_le_one (X : Matrix I (Fin k) ℝ) (hX : Xᵀ * X = 1) :
    ‖(1 : Matrix I I ℝ) - X * Xᵀ‖ ≤ 1 := by
  set P : Matrix I I ℝ := 1 - X * Xᵀ
  have hPP : Pᵀ * P = P := by
    simp only [P, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one]
    rw [Matrix.mul_assoc X Xᵀ (X * Xᵀ), ← Matrix.mul_assoc Xᵀ X, hX, Matrix.one_mul]
    abel
  rw [← norm_indexedMatCLM]
  refine (indexedMatCLM P).opNorm_le_bound (by norm_num) fun x => ?_
  rw [indexedMatCLM_apply]
  change coordNorm (P *ᵥ WithLp.ofLp x) ≤ 1 * ‖x‖
  set v := WithLp.ofLp x
  have hright : coordNorm v = ‖x‖ := rfl
  have hsq : coordNorm (P *ᵥ v) ^ 2 ≤ coordNorm v ^ 2 := by
    rw [coordNorm_sq, coordNorm_sq]
    have h1 : (P *ᵥ v) ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ v) := by
      rw [← Matrix.dotProduct_transpose_mulVec P v (P *ᵥ v), Matrix.mulVec_mulVec, hPP]
    have h2 : v ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ v - (Xᵀ *ᵥ v) ⬝ᵥ (Xᵀ *ᵥ v) := by
      simp only [P, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
      rw [← Matrix.mulVec_mulVec, ← Matrix.dotProduct_transpose_mulVec Xᵀ v (Xᵀ *ᵥ v),
        Matrix.transpose_transpose]
    have h3 : 0 ≤ (Xᵀ *ᵥ v) ⬝ᵥ (Xᵀ *ᵥ v) := by
      rw [← coordNorm_sq]; positivity
    linarith
  rw [one_mul, ← hright]
  nlinarith [coordNorm_nonneg (P *ᵥ v), coordNorm_nonneg v]

theorem backwardDelta_norm (A : Matrix I I ℝ) (X E : Matrix I (Fin k) ℝ)
    (T : Mat k k) (hA : Aᵀ = A) (hT : Tᵀ = T) (hX : Xᵀ * X = 1)
    (hXE : Xᵀ * E = Xᵀ * A * X - T) :
    ‖backwardCorrected A X E T - A‖ ≤ 2 * ‖E‖ := by
  have hXn := indexed_norm_le_one_of_gram X hX
  have hXt : ‖Xᵀ‖ ≤ 1 := by rw [indexed_norm_transpose]; exact hXn
  have hEt : ‖Eᵀ‖ = ‖E‖ := indexed_norm_transpose E
  have hP := norm_one_sub_mul_transpose_le_one X hX
  rw [backwardDelta_projector A X E T hA hT hXE]
  calc
    ‖-(E * Xᵀ) - X * Eᵀ * (1 - X * Xᵀ)‖ ≤ ‖E * Xᵀ‖ + ‖X * Eᵀ * (1 - X * Xᵀ)‖ := by
      simpa using norm_sub_le (-(E * Xᵀ)) (X * Eᵀ * (1 - X * Xᵀ))
    _ ≤ ‖E‖ * ‖Xᵀ‖ + ‖X‖ * ‖Eᵀ‖ * ‖(1 : Matrix I I ℝ) - X * Xᵀ‖ := by
      gcongr
      · exact Matrix.l2_opNorm_mul _ _
      · exact (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ ‖E‖ * 1 + 1 * ‖E‖ * 1 := by
      rw [hEt]; gcongr
    _ = 2 * ‖E‖ := by ring

theorem backwardDelta_compression (A : Matrix I I ℝ) (X E : Matrix I (Fin k) ℝ)
    (T : Mat k k) (hA : Aᵀ = A) (hT : Tᵀ = T) (hX : Xᵀ * X = 1)
    (hXE : Xᵀ * E = Xᵀ * A * X - T) :
    (1 - X * Xᵀ) * (backwardCorrected A X E T - A) * (1 - X * Xᵀ) = 0 := by
  have h1 : Xᵀ * (1 - X * Xᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hX, Matrix.one_mul, sub_self]
  have h2 : (1 - X * Xᵀ) * X = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hX, Matrix.mul_one, sub_self]
  rw [backwardDelta_projector A X E T hA hT hXE]
  set Q : Matrix I I ℝ := 1 - X * Xᵀ
  have t1 : Q * (E * Xᵀ) * Q = 0 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_zero, Matrix.mul_zero]
  have t2 : Q * (X * Eᵀ * Q) * Q = 0 := by
    rw [Matrix.mul_assoc X, ← Matrix.mul_assoc Q X, h2, Matrix.zero_mul, Matrix.zero_mul]
  rw [Matrix.mul_sub Q, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, t1, t2, neg_zero,
    sub_zero]

theorem backwardDelta_mul (A : Matrix I I ℝ) (X E : Matrix I (Fin k) ℝ)
    (T : Mat k k) (hA : Aᵀ = A) (hT : Tᵀ = T) (hX : Xᵀ * X = 1)
    (hXE : Xᵀ * E = Xᵀ * A * X - T) :
    (backwardCorrected A X E T - A) * X = -E := by
  rw [backwardDelta_projector A X E T hA hT hXE]
  simp only [Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_assoc, Matrix.one_mul, hX,
    Matrix.mul_one, sub_self, Matrix.mul_zero, sub_zero]

/-- The correction has rank at most 2k: factor its projector form through k+k columns. -/
theorem backwardDelta_rank (A : Matrix I I ℝ) (X E : Matrix I (Fin k) ℝ)
    (T : Mat k k) (hA : Aᵀ = A) (hT : Tᵀ = T)
    (hXE : Xᵀ * E = Xᵀ * A * X - T) :
    (backwardCorrected A X E T - A).rank ≤ 2 * k := by
  rw [backwardDelta_projector A X E T hA hT hXE]
  have hfactor : -(E * Xᵀ) - X * Eᵀ * (1 - X * Xᵀ) =
      Matrix.fromCols (-E) (-X) * Matrix.fromRows Xᵀ (Eᵀ * (1 - X * Xᵀ)) := by
    rw [Matrix.fromCols_mul_fromRows]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
    abel
  rw [hfactor]
  exact (Matrix.rank_mul_le_left _ _).trans
    (by simpa [two_mul] using Matrix.rank_le_card_width (Matrix.fromCols (-E) (-X)))

end FinitePrecisionLanczos
