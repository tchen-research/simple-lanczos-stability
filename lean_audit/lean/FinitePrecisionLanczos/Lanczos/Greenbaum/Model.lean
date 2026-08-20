import FinitePrecisionLanczos.Lanczos.Greenbaum.Measure









namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)


structure GreenbaumModel where
  d : ℕ
  U : Matrix (Fin k × Fin n) (Fin k ⊕ Fin d) ℝ
  Ttilde : Matrix (Fin k ⊕ Fin d) (Fin k ⊕ Fin d) ℝ
  dimension : Fintype.card (Fin k × Fin n) = k + d
  transpose_mul_self : Matrix.transpose U * U = 1
  mul_transpose : U * Matrix.transpose U = 1
  first_columns : ∀ r i, U r (Sum.inl i) = L.greenbaumX r i
  Ttilde_symmetric : Matrix.transpose Ttilde = Ttilde
  Ttilde_tridiagonal : Matrix.SumUpperTridiagonal Ttilde
  leading_block : ∀ i j, Ttilde (Sum.inl i) (Sum.inl j) = L.Tmat i j
  operator_bound :
    ‖Matrix.transpose U * L.greenbaumBlockOperator * U - Ttilde‖ ≤
      3 * ‖L.greenbaumError‖
  explicit_operator_bound :
    ‖Matrix.transpose U * L.greenbaumBlockOperator * U - Ttilde‖ ≤
      (3000000 * (k : ℝ) ^ 8) * L.ε * ‖L.H‖


noncomputable def GreenbaumModel.S (M : L.GreenbaumModel) :
    Matrix (Fin k ⊕ Fin M.d) (Fin k ⊕ Fin M.d) ℝ :=
  Matrix.transpose M.U * L.greenbaumBlockOperator * M.U


noncomputable def GreenbaumModel.delta (M : L.GreenbaumModel) : ℝ :=
  ‖M.S - M.Ttilde‖


theorem exists_greenbaumModel : Nonempty L.GreenbaumModel := by
  obtain ⟨d, U, Ttilde, hdim, hUtU, hUUt, hprefix, hsymm, htri,
    hlead, _hcoord, hbound, hexplicit⟩ := L.greenbaum_exact_completion
  exact ⟨{
    d := d
    U := U
    Ttilde := Ttilde
    dimension := hdim
    transpose_mul_self := hUtU
    mul_transpose := hUUt
    first_columns := hprefix
    Ttilde_symmetric := hsymm
    Ttilde_tridiagonal := htri
    leading_block := hlead
    operator_bound := hbound
    explicit_operator_bound := hexplicit
  }⟩

namespace GreenbaumModel

variable (M : L.GreenbaumModel)


theorem S_symmetric : Matrix.transpose M.S = M.S := by
  simp [S, Matrix.transpose_mul, L.greenbaumBlockOperator_transpose,
    Matrix.mul_assoc]


theorem S_orthogonal_similarity :
    M.S = Matrix.transpose M.U * L.greenbaumBlockOperator * M.U := rfl




theorem U_first :
    Matrix.mulVec M.U (completionFirst L.hk_pos M.d) =
      physicalFirst L.hk_pos L.normalizedV := by
  calc
    Matrix.mulVec M.U (completionFirst L.hk_pos M.d) =
        fun r => M.U r (Sum.inl (⟨0, L.hk_pos⟩ : Fin k)) :=
      L.mulVec_completionFirst M.U
    _ = fun r => L.greenbaumX r (⟨0, L.hk_pos⟩ : Fin k) := by
      funext r
      exact M.first_columns r (⟨0, L.hk_pos⟩ : Fin k)
    _ = physicalFirst L.hk_pos L.normalizedV := L.greenbaumX_first_column


theorem delta_le_error : M.delta ≤ 3 * ‖L.greenbaumError‖ := by
  exact M.operator_bound


theorem delta_explicit :
    M.delta ≤ (3000000 * (k : ℝ) ^ 8) * L.ε * ‖L.H‖ := by
  exact M.explicit_operator_bound


theorem prescribed_subdiagonal_positive (j : Fin (k - 1)) :
    0 < M.Ttilde
      (Sum.inl (⟨j.1 + 1, by omega⟩ : Fin k))
      (Sum.inl (⟨j.1, by omega⟩ : Fin k)) := by
  rw [M.leading_block]
  have hb := L.hβ_internal (j.1 + 1) (by omega) (by omega)
  have hback : ¬j.1 + 1 + 1 = j.1 := by omega
  simpa [Tmat, hback] using hb


theorem starting_moment (m : ℕ) :
    completionFirst L.hk_pos M.d ⬝ᵥ
        Matrix.mulVec (M.S ^ m) (completionFirst L.hk_pos M.d) =
      L.normalizedStart ⬝ᵥ Matrix.mulVec (L.H ^ m) L.normalizedStart := by
  exact L.greenbaum_starting_moment M.U M.transpose_mul_self M.mul_transpose
    M.first_columns m



theorem eigenvalue_localization (i : Fin k ⊕ Fin M.d) :
    spectralDistance L.H
        ((indexed_isHermitian_of_transpose_eq M.Ttilde_symmetric).eigenvalues i) ≤
      M.delta := by
  exact L.completed_eigenvalue_localization M.U M.transpose_mul_self
    M.mul_transpose M.Ttilde M.Ttilde_symmetric i


theorem eigenvalue_localization_explicit (i : Fin k ⊕ Fin M.d) :
    spectralDistance L.H
        ((indexed_isHermitian_of_transpose_eq M.Ttilde_symmetric).eigenvalues i) ≤
      (3000000 * (k : ℝ) ^ 8) * L.ε * ‖L.H‖ :=
  (eigenvalue_localization L M i).trans (delta_explicit L M)

end GreenbaumModel
end LanczosRun
end FinitePrecisionLanczos
