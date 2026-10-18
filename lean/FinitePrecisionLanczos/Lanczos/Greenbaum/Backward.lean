import FinitePrecisionLanczos.Lanczos.Greenbaum.Correction
import FinitePrecisionLanczos.Core.ExactLanczos


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

lemma Tmat_eq_tridiag : L.Tmat = tridiag k L.α L.β := rfl

theorem greenbaum_orthonormalRecurrence :
    OrthonormalRecurrence L.greenbaumTildeA (colSeq L.greenbaumVhat) L.α L.β k :=
  orthonormalRecurrence_of_matrix L.greenbaumTildeA L.greenbaumVhat L.α L.β L.hβ_zero
    L.hβ_internal (L.hβ_nonneg k le_rfl) L.physical_dilation.orthonormal
    L.greenbaum_corrected_recurrence

lemma colSeq_greenbaumVhat_one : colSeq L.greenbaumVhat 1 = L.greenbaumStart := by
  rw [colSeq_succ _ (Nat.zero_le k)]
  exact L.greenbaumVhat_column_zero

structure GreenbaumBackwardModel : Prop where
  dimension : Fintype.card (Fin (k + 1) × Fin n) = n * (k + 1)
  symmetric : L.greenbaumTildeAᵀ = L.greenbaumTildeA
  perturbation :
    ‖L.greenbaumBlockOperator - L.greenbaumTildeA‖ ≤ (480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖
  recurrence : L.greenbaumTildeA * L.greenbaumX = L.greenbaumVhat * L.underlineTmat
  orthonormal : L.greenbaumVhatᵀ * L.greenbaumVhat = 1
  start : L.greenbaumX *ᵥ firstCoord L.hk_pos = L.greenbaumStart
  exact_T : exactLanczosT L.greenbaumTildeA L.greenbaumStart k = L.Tmat
  exact_beta : exactLanczosBeta L.greenbaumTildeA L.greenbaumStart k = L.β k
  no_breakdown : ∀ j, 1 ≤ j → j < k →
    0 < exactLanczosBeta L.greenbaumTildeA L.greenbaumStart j
  exact_vectors : ∀ i : Fin k,
    exactLanczosVec L.greenbaumTildeA L.greenbaumStart (i.1 + 1) = fun a => L.greenbaumX a i
  exact_next : 0 < L.β k →
    exactLanczosVec L.greenbaumTildeA L.greenbaumStart (k + 1) = L.greenbaumVNext

theorem greenbaum_backward_model : L.GreenbaumBackwardModel := by
  have hR := (L.greenbaum_orthonormalRecurrence).exactLanczos L.hk_pos
  rw [L.colSeq_greenbaumVhat_one] at hR
  obtain ⟨hvec, -, hbeta, hpos, hnext, hT⟩ := hR
  exact {
    dimension := by simp [Nat.mul_comm]
    symmetric := L.greenbaumTildeA_transpose
    perturbation := L.greenbaumTildeA_dist
    recurrence := L.greenbaum_corrected_recurrence
    orthonormal := L.physical_dilation.orthonormal
    start := L.greenbaumX_first_eq_start
    exact_T := by rw [hT]; rfl
    exact_beta := hbeta k le_rfl
    no_breakdown := hpos
    exact_vectors := fun i => by
      rw [hvec (i.1 + 1) i.isLt, colSeq_succ _ i.isLt.le]
      rfl
    exact_next := fun hβ => by
      rw [hnext hβ, colSeq_succ _ le_rfl]
      rfl }

end LanczosRun
end FinitePrecisionLanczos
