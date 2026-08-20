import FinitePrecisionLanczos.Core.CompletionCorrection

/-!
# Symmetric correction for the physical dilation

This specializes `eq:symmetric-correction` to the actual dilated Lanczos
recurrence.  After the correction, the leading `k` columns satisfy an exact
Lanczos relation with the computed `T_k`.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

noncomputable def greenbaumDelta :
    Matrix (Fin k × Fin n) (Fin k × Fin n) ℝ :=
  symmetricCorrection L.greenbaumX L.greenbaumError

noncomputable def greenbaumCorrectedOperator :
    Matrix (Fin k × Fin n) (Fin k × Fin n) ℝ :=
  L.greenbaumBlockOperator + L.greenbaumDelta

lemma greenbaumBlockOperator_transpose :
    L.greenbaumBlockOperatorᵀ = L.greenbaumBlockOperator := by
  ext ri sj
  rcases ri with ⟨r, i⟩
  rcases sj with ⟨s, j⟩
  have hHij := congrArg (fun M : Mat n n => M i j) L.hHsymm
  simp only [Matrix.transpose_apply] at hHij ⊢
  by_cases hrs : r = s
  · subst s
    simp [greenbaumBlockOperator, blockDiagonal, hHij]
  · have hsr : s ≠ r := Ne.symm hrs
    simp [greenbaumBlockOperator, blockDiagonal, hrs, hsr]

lemma greenbaum_projected_error_symmetric :
    (L.greenbaumXᵀ * L.greenbaumError)ᵀ =
      L.greenbaumXᵀ * L.greenbaumError := by
  exact projected_error_symmetric L.hk_pos L.greenbaumBlockOperator
    L.greenbaumX L.greenbaumError L.Tmat L.greenbaumP L.normalizedBeta
    L.greenbaumBlockOperator_transpose L.Tmat_transpose
    L.greenbaumX_orthonormal L.greenbaumX_transpose_mul_P
    L.greenbaum_dilation_recurrence

theorem greenbaumDelta_transpose : L.greenbaumDeltaᵀ = L.greenbaumDelta := by
  exact symmetricCorrection_transpose L.greenbaumX L.greenbaumError
    L.greenbaum_projected_error_symmetric

theorem greenbaumCorrectedOperator_transpose :
    L.greenbaumCorrectedOperatorᵀ = L.greenbaumCorrectedOperator := by
  simp [greenbaumCorrectedOperator, Matrix.transpose_add,
    L.greenbaumBlockOperator_transpose, L.greenbaumDelta_transpose]

theorem greenbaumDelta_mul_X :
    L.greenbaumDelta * L.greenbaumX = -L.greenbaumError := by
  exact symmetricCorrection_mul L.greenbaumX L.greenbaumError
    L.greenbaumX_orthonormal L.greenbaum_projected_error_symmetric

/-- Exact corrected relation used by `lem:completion`. -/
theorem greenbaum_corrected_recurrence :
    L.greenbaumCorrectedOperator * L.greenbaumX =
      L.greenbaumX * L.Tmat +
        L.normalizedBeta • lastOuter L.hk_pos L.greenbaumP := by
  rw [greenbaumCorrectedOperator, Matrix.add_mul,
    L.greenbaum_dilation_recurrence, L.greenbaumDelta_mul_X]
  module

theorem greenbaumDelta_norm : ‖L.greenbaumDelta‖ ≤ 3 * ‖L.greenbaumError‖ := by
  exact symmetricCorrection_norm L.greenbaumX L.greenbaumError
    L.greenbaumX_orthonormal

/-- Explicit perturbation bound before `lem:completion`. -/
theorem greenbaumDelta_bound :
    ‖L.greenbaumDelta‖ ≤
      (3000000 * (k : ℝ) ^ 8) * L.ε * ‖L.H‖ := by
  calc
    ‖L.greenbaumDelta‖ ≤ 3 * ‖L.greenbaumError‖ := L.greenbaumDelta_norm
    _ ≤ 3 * ((1000000 * (k : ℝ) ^ 8) * L.ε * ‖L.H‖) :=
      mul_le_mul_of_nonneg_left L.greenbaumError_bound (by norm_num)
    _ = (3000000 * (k : ℝ) ^ 8) * L.ε * ‖L.H‖ := by ring

end LanczosRun
end FinitePrecisionLanczos
