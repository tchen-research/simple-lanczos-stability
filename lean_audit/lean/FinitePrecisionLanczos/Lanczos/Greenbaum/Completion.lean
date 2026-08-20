import FinitePrecisionLanczos.Core.Completion











namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)


def completionFirst (hk : 0 < k) (d : ℕ) : Fin k ⊕ Fin d → ℝ :=
  Pi.single (Sum.inl (⟨0, hk⟩ : Fin k)) 1



lemma mulVec_completionFirst {d : ℕ}
    (U : Matrix (Fin k × Fin n) (Fin k ⊕ Fin d) ℝ) :
    Matrix.mulVec U (completionFirst L.hk_pos d) =
      fun r => U r (Sum.inl (⟨0, L.hk_pos⟩ : Fin k)) := by
  classical
  ext r
  simp [Matrix.mulVec, completionFirst, dotProduct, Pi.single_apply]



lemma greenbaumX_first_column :
    (fun r => L.greenbaumX r (⟨0, L.hk_pos⟩ : Fin k)) =
      physicalFirst L.hk_pos L.normalizedV := by
  have h := L.greenbaumX_first
  ext r
  have hr := congrFun h r
  simpa [Matrix.mulVec, firstCoord, dotProduct, Pi.single_apply] using hr



theorem Tmat_upperTridiagonal : Matrix.UpperTridiagonal L.Tmat := by
  intro i j hij
  have hne : i ≠ j := by
    intro h
    subst j
    omega
  have hforward : ¬i.1 + 1 = j.1 := by omega
  have hbackward : ¬j.1 + 1 = i.1 := by omega
  simp [Tmat, hne, hforward, hbackward]



theorem greenbaum_corrected_recurrence_boundary :
    L.greenbaumCorrectedOperator * L.greenbaumX =
      L.greenbaumX * L.Tmat +
        lastOuter L.hk_pos (L.normalizedBeta • L.greenbaumP) := by
  rw [lastOuter_smul]
  exact L.greenbaum_corrected_recurrence



theorem greenbaum_boundary_orthogonal :
    Matrix.mulVec (Matrix.transpose L.greenbaumX)
      (L.normalizedBeta • L.greenbaumP) = 0 := by
  rw [Matrix.mulVec_smul, L.greenbaumX_transpose_mul_P, smul_zero]







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
