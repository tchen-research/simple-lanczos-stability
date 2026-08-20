import FinitePrecisionLanczos.Lanczos.Greenbaum.Model
import FinitePrecisionLanczos.Core.Measure.SpectralMass

/-!
# Exact starting spectral measure

This optional extension turns the all-moments identity into literal equality
of finite atomic spectral mass functions
without an appeal to an unformalized moment-determinacy principle.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace LanczosRun.GreenbaumModel

variable {n k : ℕ} (L : LanczosRun n k) (M : L.GreenbaumModel)

/-- Literal equality of the two finite starting spectral masses. -/
theorem starting_spectralMass :
    spectralMass M.S (indexed_isHermitian_of_transpose_eq M.S_symmetric)
        (completionFirst L.hk_pos M.d) =
      spectralMass L.H (isHermitian_of_transpose_eq L.hHsymm)
        L.normalizedStart := by
  apply atomicMass_ext_moments
  intro m
  rw [atomicMoment_spectralMass, atomicMoment_spectralMass]
  exact starting_moment L M m

end LanczosRun.GreenbaumModel
end FinitePrecisionLanczos
