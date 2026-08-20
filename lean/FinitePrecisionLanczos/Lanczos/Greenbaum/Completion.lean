import FinitePrecisionLanczos.Core.Completion

/-!
# Exact completion of the corrected Greenbaum dilation

This file instantiates the exact continuation/restart theorem with the
corrected physical dilation.  It is the formal counterpart of
`lem:completion`: the computed `T_k` is the exact
leading block of a symmetric tridiagonal matrix, while the corresponding
operator is close to `I_k \otimes H` in operator norm.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- First standard coordinate of a completed index set. -/
def completionFirst (hk : 0 < k) (d : ℕ) : Fin k ⊕ Fin d → ℝ :=
  Pi.single (Sum.inl (⟨0, hk⟩ : Fin k)) 1

/-- Multiplication by the first coordinate selects the first prescribed
column. -/
lemma mulVec_completionFirst {d : ℕ}
    (U : Matrix (Fin k × Fin n) (Fin k ⊕ Fin d) ℝ) :
    Matrix.mulVec U (completionFirst L.hk_pos d) =
      fun r => U r (Sum.inl (⟨0, L.hk_pos⟩ : Fin k)) := by
  classical
  ext r
  simp [Matrix.mulVec, completionFirst, dotProduct, Pi.single_apply]

/-- The first column of the physical dilation is the normalized starting
vector in the first physical copy. -/
lemma greenbaumX_first_column :
    (fun r => L.greenbaumX r (⟨0, L.hk_pos⟩ : Fin k)) =
      physicalFirst L.hk_pos L.normalizedV := by
  have h := L.greenbaumX_first
  ext r
  have hr := congrFun h r
  simpa [Matrix.mulVec, firstCoord, dotProduct, Pi.single_apply] using hr

/-- The computed coefficient matrix has the tridiagonal zero pattern needed
by exact continuation. -/
theorem Tmat_upperTridiagonal : Matrix.UpperTridiagonal L.Tmat := by
  intro i j hij
  have hne : i ≠ j := by
    intro h
    subst j
    omega
  have hforward : ¬i.1 + 1 = j.1 := by omega
  have hbackward : ¬j.1 + 1 = i.1 := by omega
  simp [Tmat, hne, hforward, hbackward]

/-- The corrected physical recurrence in the boundary-vector form consumed
by the exact completion theorem. -/
theorem greenbaum_corrected_recurrence_boundary :
    L.greenbaumCorrectedOperator * L.greenbaumX =
      L.greenbaumX * L.Tmat +
        lastOuter L.hk_pos (L.normalizedBeta • L.greenbaumP) := by
  rw [lastOuter_smul]
  exact L.greenbaum_corrected_recurrence

/-- The corrected boundary vector remains orthogonal to the prescribed
columns. -/
theorem greenbaum_boundary_orthogonal :
    Matrix.mulVec (Matrix.transpose L.greenbaumX)
      (L.normalizedBeta • L.greenbaumP) = 0 := by
  rw [Matrix.mulVec_smul, L.greenbaumX_transpose_mul_P, smul_zero]

/-- `lem:completion`, in explicit matrix coordinates.

The matrix `U` is the standard-coordinate matrix of `b`, and the completed
tridiagonal matrix is the coordinate matrix of the corrected operator in
that basis.  The statement preserves the first `k` columns exactly and
identifies the computed `T_k` entry by entry as the leading block. -/
theorem greenbaum_exact_completion_basis :
    ∃ d : ℕ,
      ∃ b : OrthonormalBasis (Fin k ⊕ Fin d) ℝ
          (EuclideanSpace ℝ (Fin k × Fin n)),
        Fintype.card (Fin k × Fin n) = k + d ∧
        (∀ i, b (Sum.inl i) = euclideanColumn L.greenbaumX i) ∧
        Matrix.SumUpperTridiagonal
          (operatorInBasis (euclideanOperator L.greenbaumCorrectedOperator) b) ∧
        (∀ i j,
          operatorInBasis (euclideanOperator L.greenbaumCorrectedOperator) b
              (Sum.inl i) (Sum.inl j) = L.Tmat i j) := by
  exact exists_matrix_exact_completion_basis L.hk_pos
    L.greenbaumCorrectedOperator L.greenbaumCorrectedOperator_transpose
    L.greenbaumX L.greenbaumX_orthonormal L.Tmat L.Tmat_upperTridiagonal
    (L.normalizedBeta • L.greenbaumP) L.greenbaum_boundary_orthogonal
    L.greenbaum_corrected_recurrence_boundary

/-- Matrix-only form of `lem:completion`.

The completed matrix is symmetric and tridiagonal, its leading block is the
computed `T_k`, and it differs from an orthogonal copy of
`I_k \otimes H` by at most the displayed correction. -/
theorem greenbaum_exact_completion :
    ∃ d : ℕ,
      ∃ U : Matrix (Fin k × Fin n) (Fin k ⊕ Fin d) ℝ,
      ∃ Ttilde : Matrix (Fin k ⊕ Fin d) (Fin k ⊕ Fin d) ℝ,
        Fintype.card (Fin k × Fin n) = k + d ∧
        Matrix.transpose U * U = 1 ∧
        U * Matrix.transpose U = 1 ∧
        (∀ r i, U r (Sum.inl i) = L.greenbaumX r i) ∧
        Matrix.transpose Ttilde = Ttilde ∧
        Matrix.SumUpperTridiagonal Ttilde ∧
        (∀ i j, Ttilde (Sum.inl i) (Sum.inl j) = L.Tmat i j) ∧
        Ttilde = Matrix.transpose U * L.greenbaumCorrectedOperator * U ∧
        ‖Matrix.transpose U * L.greenbaumBlockOperator * U - Ttilde‖ ≤
          3 * ‖L.greenbaumError‖ ∧
        ‖Matrix.transpose U * L.greenbaumBlockOperator * U - Ttilde‖ ≤
          (3000000 * (k : ℝ) ^ 8) * L.ε * ‖L.H‖ := by
  obtain ⟨d, b, hdim, hb, htri, hlead⟩ :=
    L.greenbaum_exact_completion_basis
  let U : Matrix (Fin k × Fin n) (Fin k ⊕ Fin d) ℝ :=
    orthonormalBasisMatrix b
  let Ttilde : Matrix (Fin k ⊕ Fin d) (Fin k ⊕ Fin d) ℝ :=
    operatorInBasis (euclideanOperator L.greenbaumCorrectedOperator) b
  have hUtU : Matrix.transpose U * U = 1 := by
    exact orthonormalBasisMatrix_transpose_mul_self b
  have hUUt : U * Matrix.transpose U = 1 := by
    exact orthonormalBasisMatrix_mul_transpose b
  have hprefix : ∀ r i, U r (Sum.inl i) = L.greenbaumX r i := by
    intro r i
    rw [show U r (Sum.inl i) = b (Sum.inl i) r by
      exact orthonormalBasisMatrix_apply b r (Sum.inl i)]
    rw [hb i]
    rfl
  have hoperatorSymm :
      (euclideanOperator L.greenbaumCorrectedOperator).IsSymmetric :=
    euclideanOperator_isSymmetric L.greenbaumCorrectedOperator
      L.greenbaumCorrectedOperator_transpose
  have hTtranspose : Matrix.transpose Ttilde = Ttilde := by
    exact operatorInBasis_transpose
      (euclideanOperator L.greenbaumCorrectedOperator) hoperatorSymm b
  have hcoord :
      Ttilde = Matrix.transpose U * L.greenbaumCorrectedOperator * U := by
    exact operatorInBasis_euclideanOperator_eq
      L.greenbaumCorrectedOperator b
  have hdiff :
      Matrix.transpose U * L.greenbaumBlockOperator * U - Ttilde =
        -(Matrix.transpose U * L.greenbaumDelta * U) := by
    rw [hcoord, greenbaumCorrectedOperator]
    rw [Matrix.mul_add, Matrix.add_mul]
    module
  have hUnorm : ‖U‖ ≤ 1 := indexed_norm_le_one_of_gram U hUtU
  have hUtnorm : ‖Matrix.transpose U‖ ≤ 1 := by
    rw [indexed_norm_transpose]
    exact hUnorm
  have hcorrection :
      ‖Matrix.transpose U * L.greenbaumBlockOperator * U - Ttilde‖ ≤
        ‖L.greenbaumDelta‖ := by
    rw [hdiff, norm_neg]
    calc
      ‖Matrix.transpose U * L.greenbaumDelta * U‖ ≤
          ‖Matrix.transpose U * L.greenbaumDelta‖ * ‖U‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Matrix.transpose U‖ * ‖L.greenbaumDelta‖) * ‖U‖ := by
        exact mul_le_mul_of_nonneg_right
          (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (1 * ‖L.greenbaumDelta‖) * 1 := by gcongr
      _ = ‖L.greenbaumDelta‖ := by ring
  have herror :
      ‖Matrix.transpose U * L.greenbaumBlockOperator * U - Ttilde‖ ≤
        3 * ‖L.greenbaumError‖ :=
    hcorrection.trans L.greenbaumDelta_norm
  have hexplicit :
      ‖Matrix.transpose U * L.greenbaumBlockOperator * U - Ttilde‖ ≤
        (3000000 * (k : ℝ) ^ 8) * L.ε * ‖L.H‖ :=
    hcorrection.trans L.greenbaumDelta_bound
  refine ⟨d, U, Ttilde, hdim, hUtU, hUUt, hprefix,
    hTtranspose, ?_, ?_, hcoord, herror, hexplicit⟩
  · exact htri
  · exact hlead

end LanczosRun
end FinitePrecisionLanczos
