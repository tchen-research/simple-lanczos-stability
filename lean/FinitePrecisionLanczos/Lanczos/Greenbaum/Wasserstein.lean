import FinitePrecisionLanczos.Lanczos.Greenbaum.SpectralMass
import FinitePrecisionLanczos.Core.Measure.FunctionalCalculus


namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

theorem greenbaumDelta_compression :
    (1 - L.greenbaumX * L.greenbaumXᵀ) * L.greenbaumDelta *
        (1 - L.greenbaumX * L.greenbaumXᵀ) = 0 :=
  backwardDelta_compression _ _ _ _ L.greenbaumBlockOperator_transpose L.Tmat_transpose
    L.greenbaumX_orthonormal L.greenbaum_projected_error

theorem greenbaumDelta_frobNorm_le :
    frobNorm L.greenbaumDelta ≤ Real.sqrt (2 * k) * ‖L.greenbaumDelta‖ := by
  have hr : (L.greenbaumDelta.rank : ℝ) ≤ 2 * k := by exact_mod_cast L.greenbaumDelta_rank
  exact (frobNorm_le_sqrt_rank L.greenbaumDelta
    (indexed_isHermitian_of_transpose_eq L.greenbaumDelta_transpose)).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hr) (norm_nonneg _))

/-- The first functional-calculus identity in the paper's spectral-measure remark. -/
theorem starting_functional_calculus (f : ℝ → ℝ) :
    L.normalizedStart ⬝ᵥ ((cfc f L.H) *ᵥ L.normalizedStart) =
      L.greenbaumStart ⬝ᵥ ((cfc f L.greenbaumBlockOperator) *ᵥ L.greenbaumStart) := by
  rw [← atomicIntegral_spectralMass_cfc L.H (isHermitian_of_transpose_eq L.hHsymm),
    ← atomicIntegral_spectralMass_cfc L.greenbaumBlockOperator
      (indexed_isHermitian_of_transpose_eq L.greenbaumBlockOperator_transpose),
    L.starting_spectralMass]

/-- The pointwise Lipschitz estimate, through the full matrix functional calculus. -/
theorem starting_lipschitz_frobNorm (f : ℝ → ℝ) (hf : OneLipschitz f) :
    |L.normalizedStart ⬝ᵥ ((cfc f L.H) *ᵥ L.normalizedStart) -
      L.greenbaumStart ⬝ᵥ ((cfc f L.greenbaumTildeA) *ᵥ L.greenbaumStart)| ≤
      frobNorm L.greenbaumDelta := by
  rw [L.starting_functional_calculus]
  have h := cfc_quadratic_lipschitz L.greenbaumBlockOperator L.greenbaumTildeA
    (indexed_isHermitian_of_transpose_eq L.greenbaumBlockOperator_transpose)
    (indexed_isHermitian_of_transpose_eq L.greenbaumTildeA_transpose)
    L.greenbaumStart L.greenbaumStart_unit f hf
  rwa [← frobNorm_neg, neg_sub] at h

theorem starting_lipschitz (f : ℝ → ℝ) (hf : OneLipschitz f) :
    |L.normalizedStart ⬝ᵥ ((cfc f L.H) *ᵥ L.normalizedStart) -
      L.greenbaumStart ⬝ᵥ ((cfc f L.greenbaumTildeA) *ᵥ L.greenbaumStart)| ≤
      Real.sqrt (2 * k) * ‖L.greenbaumDelta‖ :=
  (L.starting_lipschitz_frobNorm f hf).trans L.greenbaumDelta_frobNorm_le

theorem starting_wasserstein_frobNorm :
    atomicWasserstein
        (spectralMass L.H (isHermitian_of_transpose_eq L.hHsymm) L.normalizedStart)
        (spectralMass L.greenbaumTildeA
          (indexed_isHermitian_of_transpose_eq L.greenbaumTildeA_transpose)
          L.greenbaumStart) ≤
      frobNorm L.greenbaumDelta := by
  apply atomicWasserstein_le
  intro f hf
  rw [atomicIntegral_spectralMass_cfc, atomicIntegral_spectralMass_cfc]
  exact L.starting_lipschitz_frobNorm f hf

theorem starting_wasserstein :
    atomicWasserstein
        (spectralMass L.H (isHermitian_of_transpose_eq L.hHsymm) L.normalizedStart)
        (spectralMass L.greenbaumTildeA
          (indexed_isHermitian_of_transpose_eq L.greenbaumTildeA_transpose)
          L.greenbaumStart) ≤
      Real.sqrt (2 * k) * ‖L.greenbaumDelta‖ :=
  L.starting_wasserstein_frobNorm.trans L.greenbaumDelta_frobNorm_le

theorem starting_wasserstein_explicit :
    atomicWasserstein
        (spectralMass L.H (isHermitian_of_transpose_eq L.hHsymm) L.normalizedStart)
        (spectralMass L.greenbaumTildeA
          (indexed_isHermitian_of_transpose_eq L.greenbaumTildeA_transpose)
          L.greenbaumStart) ≤
      Real.sqrt (2 * k) * ((480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖) :=
  (L.starting_wasserstein).trans
    (mul_le_mul_of_nonneg_left L.greenbaumDelta_bound (Real.sqrt_nonneg _))

end LanczosRun
end FinitePrecisionLanczos
