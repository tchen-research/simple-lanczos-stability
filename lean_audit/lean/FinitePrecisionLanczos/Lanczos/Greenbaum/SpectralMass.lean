import FinitePrecisionLanczos.Lanczos.Greenbaum.Measure
import FinitePrecisionLanczos.Core.Measure.SpectralMass


namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

theorem starting_spectralMass :
    spectralMass L.greenbaumBlockOperator
        (indexed_isHermitian_of_transpose_eq L.greenbaumBlockOperator_transpose)
        L.greenbaumStart =
      spectralMass L.H (isHermitian_of_transpose_eq L.hHsymm) L.normalizedStart := by
  apply atomicMass_ext_moments
  intro m
  rw [atomicMoment_spectralMass, atomicMoment_spectralMass]
  exact L.greenbaum_starting_moment m

end LanczosRun
end FinitePrecisionLanczos
