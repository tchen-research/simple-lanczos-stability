import FinitePrecisionLanczos.Lanczos.Greenbaum.Dilation

/-!
# Symmetric backward correction

This is the first half of `lem:completion`, through
`eq:symmetric-correction`.  It is stated for arbitrary finite coordinate
types, so it applies directly to the physical product space `Fin k × Fin n`.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

variable {I J : Type*} [Fintype I] [Fintype J]

/-- A generic finite matrix with orthonormal columns has operator norm at
most one. -/
theorem indexed_norm_le_one_of_gram [DecidableEq I] [DecidableEq J]
    (X : Matrix I J ℝ) (hX : Xᵀ * X = 1) : ‖X‖ ≤ 1 := by
  rw [← norm_indexedMatCLM]
  refine (indexedMatCLM X).opNorm_le_bound (by norm_num) fun x => ?_
  rw [indexedMatCLM_apply]
  change coordNorm (X *ᵥ WithLp.ofLp x) ≤ 1 * ‖x‖
  have hsq : coordNorm (X *ᵥ WithLp.ofLp x) ^ 2 =
      coordNorm (WithLp.ofLp x) ^ 2 := by
    rw [coordNorm_sq, coordNorm_sq]
    calc
      (X *ᵥ WithLp.ofLp x) ⬝ᵥ (X *ᵥ WithLp.ofLp x) =
          WithLp.ofLp x ⬝ᵥ Xᵀ *ᵥ (X *ᵥ WithLp.ofLp x) := by
        symm
        exact Matrix.dotProduct_transpose_mulVec X (WithLp.ofLp x)
          (X *ᵥ WithLp.ofLp x)
      _ = WithLp.ofLp x ⬝ᵥ ((Xᵀ * X) *ᵥ WithLp.ofLp x) := by
        rw [Matrix.mulVec_mulVec]
      _ = WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by rw [hX, Matrix.one_mulVec]
  have hleft := coordNorm_nonneg (X *ᵥ WithLp.ofLp x)
  have hright : coordNorm (WithLp.ofLp x) = ‖x‖ := rfl
  rw [one_mul, ← hright]
  have hnorm := norm_nonneg x
  nlinarith [sq_nonneg
    (coordNorm (X *ᵥ WithLp.ofLp x) + coordNorm (WithLp.ofLp x))]

lemma indexed_norm_transpose [DecidableEq I] [DecidableEq J]
    (X : Matrix I J ℝ) : ‖Xᵀ‖ = ‖X‖ := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial X]
  exact Matrix.l2_opNorm_conjTranspose X

/-- The correction in `eq:symmetric-correction`. -/
def symmetricCorrection (X E : Matrix I J ℝ) : Matrix I I ℝ :=
  -(E * Xᵀ) - X * Eᵀ + X * (Xᵀ * E) * Xᵀ

/-- Projecting a symmetric inexact recurrence onto its orthonormal columns
shows that `XᵀE` is symmetric. -/
theorem projected_error_symmetric {k : ℕ} [DecidableEq I]
    (hk : 0 < k) (A : Matrix I I ℝ)
    (X E : Matrix I (Fin k) ℝ) (T : Matrix (Fin k) (Fin k) ℝ)
    (p : I → ℝ) (b : ℝ)
    (hA : Aᵀ = A) (hT : Tᵀ = T) (hX : Xᵀ * X = 1)
    (hp : Xᵀ *ᵥ p = 0)
    (hrec : A * X = X * T + b • lastOuter hk p + E) :
    (Xᵀ * E)ᵀ = Xᵀ * E := by
  have hproj := congrArg (fun M : Matrix I (Fin k) ℝ => Xᵀ * M) hrec
  have hzero : Xᵀ * lastOuter hk p = 0 := by
    rw [lastOuter, Matrix.mul_vecMulVec, hp]
    ext i j
    simp [Matrix.vecMulVec]
  have hboundary : Xᵀ *
      (b • lastOuter hk p) = 0 := by
    rw [Matrix.mul_smul, hzero, smul_zero]
  have hleftSymm : (Xᵀ * A * X)ᵀ = Xᵀ * A * X := by
    simp [Matrix.transpose_mul, hA, Matrix.mul_assoc]
  have hproj' : Xᵀ * A * X = T + Xᵀ * E := by
    calc
      Xᵀ * A * X = Xᵀ * (A * X) := by simp [Matrix.mul_assoc]
      _ = Xᵀ * (X * T + b • lastOuter hk p + E) := hproj
      _ = Xᵀ * (X * T) + Xᵀ * (b • lastOuter hk p) + Xᵀ * E := by
        rw [Matrix.mul_add, Matrix.mul_add]
      _ = T + Xᵀ * E := by
        rw [← Matrix.mul_assoc, hX, Matrix.one_mul, hboundary, add_zero]
  have hprojT : Xᵀ * A * X = T + (Xᵀ * E)ᵀ := by
    calc
      Xᵀ * A * X = (Xᵀ * A * X)ᵀ := hleftSymm.symm
      _ = (T + Xᵀ * E)ᵀ := by rw [hproj']
      _ = T + (Xᵀ * E)ᵀ := by rw [Matrix.transpose_add, hT]
  exact add_left_cancel (hprojT.symm.trans hproj')

/-- The correction is symmetric whenever `XᵀE` is symmetric. -/
theorem symmetricCorrection_transpose [DecidableEq I] [DecidableEq J]
    (X E : Matrix I J ℝ) (hXE : (Xᵀ * E)ᵀ = Xᵀ * E) :
    (symmetricCorrection X E)ᵀ = symmetricCorrection X E := by
  simp only [symmetricCorrection, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hEX : Eᵀ * X = Xᵀ * E := by
    simpa [Matrix.transpose_mul] using hXE
  rw [hEX]
  simp only [Matrix.mul_assoc]
  noncomm_ring

/-- The correction cancels the recurrence error exactly. -/
theorem symmetricCorrection_mul [DecidableEq I] [DecidableEq J]
    (X E : Matrix I J ℝ) (hX : Xᵀ * X = 1)
    (hXE : (Xᵀ * E)ᵀ = Xᵀ * E) :
    symmetricCorrection X E * X = -E := by
  have hEX : Eᵀ * X = Xᵀ * E := by
    simpa [Matrix.transpose_mul] using hXE
  simp only [symmetricCorrection, Matrix.add_mul, Matrix.sub_mul, Matrix.neg_mul,
    Matrix.mul_assoc, hX, Matrix.mul_one, hEX]
  noncomm_ring

/-- Operator-norm estimate in `eq:symmetric-correction`. -/
theorem symmetricCorrection_norm [DecidableEq I] [DecidableEq J]
    (X E : Matrix I J ℝ) (hX : Xᵀ * X = 1) :
    ‖symmetricCorrection X E‖ ≤ 3 * ‖E‖ := by
  have hXn := indexed_norm_le_one_of_gram X hX
  have hXt : ‖Xᵀ‖ ≤ 1 := by simpa [indexed_norm_transpose] using hXn
  have hEt : ‖Eᵀ‖ = ‖E‖ := indexed_norm_transpose E
  have h1 : ‖E * Xᵀ‖ ≤ ‖E‖ := by
    calc
      ‖E * Xᵀ‖ ≤ ‖E‖ * ‖Xᵀ‖ := Matrix.l2_opNorm_mul E Xᵀ
      _ ≤ ‖E‖ * 1 := mul_le_mul_of_nonneg_left hXt (norm_nonneg _)
      _ = ‖E‖ := mul_one _
  have h2 : ‖X * Eᵀ‖ ≤ ‖E‖ := by
    calc
      ‖X * Eᵀ‖ ≤ ‖X‖ * ‖Eᵀ‖ := Matrix.l2_opNorm_mul X Eᵀ
      _ ≤ 1 * ‖Eᵀ‖ := mul_le_mul_of_nonneg_right hXn (norm_nonneg _)
      _ = ‖E‖ := by rw [hEt, one_mul]
  have h3 : ‖X * (Xᵀ * E) * Xᵀ‖ ≤ ‖E‖ := by
    calc
      ‖X * (Xᵀ * E) * Xᵀ‖ ≤
          ‖X * (Xᵀ * E)‖ * ‖Xᵀ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖X‖ * ‖Xᵀ * E‖) * ‖Xᵀ‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (‖X‖ * (‖Xᵀ‖ * ‖E‖)) * ‖Xᵀ‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
          (norm_nonneg _)
      _ ≤ (1 * (1 * ‖E‖)) * 1 := by
        gcongr
      _ = ‖E‖ := by ring
  calc
    ‖symmetricCorrection X E‖ ≤
        ‖-(E * Xᵀ) - X * Eᵀ‖ + ‖X * (Xᵀ * E) * Xᵀ‖ :=
      norm_add_le _ _
    _ ≤ (‖E * Xᵀ‖ + ‖X * Eᵀ‖) + ‖X * (Xᵀ * E) * Xᵀ‖ := by
      gcongr
      simpa using norm_sub_le (-(E * Xᵀ)) (X * Eᵀ)
    _ ≤ (‖E‖ + ‖E‖) + ‖E‖ := by gcongr
    _ = 3 * ‖E‖ := by ring

end FinitePrecisionLanczos
