import FinitePrecisionLanczos.Lanczos.Greenbaum.Model
import FinitePrecisionLanczos.Core.Measure.SpectralMass









namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace LanczosRun.GreenbaumModel

variable {n k : ℕ} (L : LanczosRun n k) (M : L.GreenbaumModel)


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
