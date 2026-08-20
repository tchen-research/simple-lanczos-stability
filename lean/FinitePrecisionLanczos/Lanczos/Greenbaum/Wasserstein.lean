import FinitePrecisionLanczos.Lanczos.Greenbaum.SpectralMass
import FinitePrecisionLanczos.Core.Measure.SpectralWasserstein

/-!
# Wasserstein conclusion for the Greenbaum model

This optional extension applies the matrix perturbation theorem to the exact
Greenbaum completion.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The first completed coordinate is a unit vector. -/
lemma coordNorm_completionFirst {k d : ℕ} (hk : 0 < k) :
    coordNorm (LanczosRun.completionFirst hk d) = 1 := by
  classical
  rw [coordNorm]
  simp [LanczosRun.completionFirst]

namespace LanczosRun.GreenbaumModel

variable {n k : ℕ} (L : LanczosRun n k) (M : L.GreenbaumModel)

/-- The completed starting spectral measure is close to the original
starting spectral measure. -/
theorem starting_wasserstein :
    atomicWasserstein
        (spectralMass L.H (isHermitian_of_transpose_eq L.hHsymm)
          L.normalizedStart)
        (spectralMass M.Ttilde
          (indexed_isHermitian_of_transpose_eq M.Ttilde_symmetric)
          (completionFirst L.hk_pos M.d)) ≤
      Real.sqrt (n * k) * M.delta := by
  have hcard : Fintype.card (Fin k ⊕ Fin M.d) = n * k := by
    simpa [Nat.mul_comm] using M.dimension.symm
  have hpert := spectralWasserstein_le M.S M.Ttilde
    (indexed_isHermitian_of_transpose_eq M.S_symmetric)
    (indexed_isHermitian_of_transpose_eq M.Ttilde_symmetric)
    (completionFirst L.hk_pos M.d)
    (coordNorm_completionFirst L.hk_pos)
  rw [M.starting_spectralMass] at hpert
  simpa [GreenbaumModel.delta, hcard] using hpert

/-- Explicit polynomial representative of the Wasserstein bound. -/
theorem starting_wasserstein_explicit :
    atomicWasserstein
        (spectralMass L.H (isHermitian_of_transpose_eq L.hHsymm)
          L.normalizedStart)
        (spectralMass M.Ttilde
          (indexed_isHermitian_of_transpose_eq M.Ttilde_symmetric)
          (completionFirst L.hk_pos M.d)) ≤
      Real.sqrt (n * k) *
        ((3000000 * (k : ℝ) ^ 8) * L.ε * ‖L.H‖) := by
  exact (starting_wasserstein L M).trans
    (mul_le_mul_of_nonneg_left (delta_explicit L M) (Real.sqrt_nonneg _))

end LanczosRun.GreenbaumModel
end FinitePrecisionLanczos
