import FinitePrecisionLanczos.Core.Measure.SpectralWasserstein
import Mathlib.LinearAlgebra.Matrix.Rank

namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- For symmetric matrices, rank counts the nonzero eigenvalues with multiplicity. -/
theorem rank_eq_card_nonzero_eigenvalues (A : Matrix I I ℝ) (hA : A.IsHermitian) :
    A.rank = Fintype.card {i // hA.eigenvalues i ≠ 0} := by
  classical
  have hd : A = (hA.eigenvectorUnitary : Matrix I I ℝ) * Matrix.diagonal hA.eigenvalues *
      star (hA.eigenvectorUnitary : Matrix I I ℝ) := by
    conv_lhs => rw [hA.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp]
  calc
    A.rank = ((hA.eigenvectorUnitary : Matrix I I ℝ) * Matrix.diagonal hA.eigenvalues *
        star (hA.eigenvectorUnitary : Matrix I I ℝ)).rank := congrArg Matrix.rank hd
    _ = (Matrix.diagonal hA.eigenvalues).rank := by
      rw [← Unitary.coe_star, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit (star hA.eigenvectorUnitary)),
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit hA.eigenvectorUnitary)]
    _ = _ := Matrix.rank_diagonal _

/-- The rank-to-Frobenius estimate used in the paper's Wasserstein proof. -/
theorem frobNorm_le_sqrt_rank (A : Matrix I I ℝ) (hA : A.IsHermitian) :
    frobNorm A ≤ Real.sqrt (A.rank : ℝ) * ‖A‖ := by
  classical
  have hs : frobSq A ≤ (A.rank : ℝ) * ‖A‖ ^ 2 := by
    rw [← sum_norm_sq_indexedMatCLM A hA.eigenvectorBasis, rank_eq_card_nonzero_eigenvalues A hA]
    calc
      ∑ i, ‖indexedMatCLM A (hA.eigenvectorBasis i)‖ ^ 2 ≤
          ∑ i, if hA.eigenvalues i = 0 then 0 else ‖A‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : hA.eigenvalues i = 0
        · have hz : indexedMatCLM A (hA.eigenvectorBasis i) = 0 := by
            apply WithLp.ofLp_injective
            change A *ᵥ ⇑(hA.eigenvectorBasis i) = 0
            simp [hA.mulVec_eigenvectorBasis i, h]
          simp [h, hz]
        · rw [if_neg h]
          apply pow_le_pow_left₀ (norm_nonneg _)
          have hb := (indexedMatCLM A).le_opNorm (hA.eigenvectorBasis i)
          simpa [norm_indexedMatCLM, hA.eigenvectorBasis.orthonormal.1 i] using hb
      _ = _ := by simp [Finset.sum_ite, Fintype.card_subtype]
  rw [frobNorm, ← Real.sqrt_sq (norm_nonneg A), ← Real.sqrt_mul (Nat.cast_nonneg A.rank)]
  exact Real.sqrt_le_sqrt hs

end FinitePrecisionLanczos
