import FinitePrecisionLanczos.Lanczos.Greenbaum.Statements
import FinitePrecisionLanczos.Core.BackwardCorrection


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

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

noncomputable def greenbaumTildeA :
    Matrix (Fin (k + 1) × Fin n) (Fin (k + 1) × Fin n) ℝ :=
  backwardCorrected L.greenbaumBlockOperator L.greenbaumX L.greenbaumError L.Tmat

noncomputable def greenbaumDelta :
    Matrix (Fin (k + 1) × Fin n) (Fin (k + 1) × Fin n) ℝ :=
  L.greenbaumTildeA - L.greenbaumBlockOperator

noncomputable def greenbaumStart : Fin (k + 1) × Fin n → ℝ :=
  physicalFirst L.hk_pos L.normalizedV

theorem greenbaumTildeA_eq :
    L.greenbaumTildeA =
      L.greenbaumBlockOperator - L.greenbaumError * L.greenbaumXᵀ -
        L.greenbaumX * L.greenbaumErrorᵀ +
        L.greenbaumX * (L.greenbaumXᵀ * L.greenbaumBlockOperator * L.greenbaumX - L.Tmat) *
          L.greenbaumXᵀ := rfl

theorem greenbaumTildeA_transpose : L.greenbaumTildeAᵀ = L.greenbaumTildeA :=
  backwardCorrected_transpose _ _ _ _ L.greenbaumBlockOperator_transpose L.Tmat_transpose

theorem greenbaum_projected_error :
    L.greenbaumXᵀ * L.greenbaumError =
      L.greenbaumXᵀ * L.greenbaumBlockOperator * L.greenbaumX - L.Tmat :=
  projected_error_eq L.greenbaumBlockOperator L.greenbaumVhat L.greenbaumError L.Tmat
    (L.β k) L.physical_dilation.orthonormal L.dilated_recurrence.recurrence

theorem greenbaumDelta_projector :
    L.greenbaumDelta =
      -(L.greenbaumError * L.greenbaumXᵀ) -
        L.greenbaumX * L.greenbaumErrorᵀ * (1 - L.greenbaumX * L.greenbaumXᵀ) :=
  backwardDelta_projector _ _ _ _ L.greenbaumBlockOperator_transpose L.Tmat_transpose
    L.greenbaum_projected_error

theorem greenbaumDelta_transpose : L.greenbaumDeltaᵀ = L.greenbaumDelta := by
  rw [greenbaumDelta, Matrix.transpose_sub, L.greenbaumTildeA_transpose,
    L.greenbaumBlockOperator_transpose]

/-- The three-term perturbation formula printed in the corrected paper. -/
theorem greenbaumDelta_eq :
    L.greenbaumDelta = -(L.greenbaumError * L.greenbaumXᵀ) -
      L.greenbaumX * L.greenbaumErrorᵀ +
      L.greenbaumX * (L.greenbaumXᵀ * L.greenbaumBlockOperator * L.greenbaumX - L.Tmat) *
        L.greenbaumXᵀ := by
  rw [greenbaumDelta, L.greenbaumTildeA_eq]
  abel

theorem greenbaumDelta_rank : L.greenbaumDelta.rank ≤ 2 * k :=
  backwardDelta_rank _ _ _ _ L.greenbaumBlockOperator_transpose L.Tmat_transpose
    L.greenbaum_projected_error

theorem greenbaumDelta_norm : ‖L.greenbaumDelta‖ ≤ 2 * ‖L.greenbaumError‖ :=
  backwardDelta_norm _ _ _ _ L.greenbaumBlockOperator_transpose L.Tmat_transpose
    L.greenbaumX_orthonormal L.greenbaum_projected_error

theorem greenbaumDelta_bound :
    ‖L.greenbaumDelta‖ ≤ (480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ := by
  have h := L.greenbaumDelta_norm
  have hE := L.dilated_recurrence.error_bound
  nlinarith

theorem greenbaumTildeA_dist :
    ‖L.greenbaumBlockOperator - L.greenbaumTildeA‖ ≤
      (480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ := by
  rw [norm_sub_rev]; exact L.greenbaumDelta_bound

theorem greenbaumDelta_mul_X : L.greenbaumDelta * L.greenbaumX = -L.greenbaumError :=
  backwardDelta_mul _ _ _ _ L.greenbaumBlockOperator_transpose L.Tmat_transpose
    L.greenbaumX_orthonormal L.greenbaum_projected_error

theorem greenbaum_corrected_recurrence :
    L.greenbaumTildeA * L.greenbaumX = L.greenbaumVhat * L.underlineTmat := by
  have hsplit : L.greenbaumTildeA = L.greenbaumBlockOperator + L.greenbaumDelta := by
    rw [greenbaumDelta]; abel
  rw [hsplit, Matrix.add_mul, L.greenbaumDelta_mul_X, L.dilated_recurrence.recurrence]
  abel

theorem greenbaumX_first_eq_start :
    L.greenbaumX *ᵥ firstCoord L.hk_pos = L.greenbaumStart := by
  rw [greenbaumStart, ← L.physical_dilation.first_column]
  funext a
  simp [greenbaumX, leadCols, Matrix.mulVec, dotProduct, firstCoord, Pi.single_apply]

theorem greenbaumVhat_column_zero :
    (fun a => L.greenbaumVhat a ⟨0, Nat.succ_pos k⟩) = L.greenbaumStart := by
  rw [greenbaumStart, ← L.physical_dilation.first_column]
  funext a
  simp [Matrix.mulVec, dotProduct, firstCoord, Pi.single_apply]

end LanczosRun
end FinitePrecisionLanczos
