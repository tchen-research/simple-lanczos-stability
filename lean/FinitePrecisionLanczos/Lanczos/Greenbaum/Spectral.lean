import FinitePrecisionLanczos.Lanczos.Greenbaum.Backward
import FinitePrecisionLanczos.Core.BlockSpectral


namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

theorem block_eigenvalue_localization {n p : ℕ}
    (hn : 0 < n) (H : Mat n n) (hH : Matrix.transpose H = H)
    (T : Matrix (Fin p × Fin n) (Fin p × Fin n) ℝ) (hT : Matrix.transpose T = T)
    (i : Fin p × Fin n) :
    spectralDistance H ((indexed_isHermitian_of_transpose_eq hT).eigenvalues i) ≤
      ‖blockDiagonal H - T‖ := by
  let hTherm : T.IsHermitian := indexed_isHermitian_of_transpose_eq hT
  let theta := hTherm.eigenvalues i
  let z : Fin p × Fin n → ℝ := ⇑(hTherm.eigenvectorBasis i)
  have hz : coordNorm z = 1 := by
    change ‖hTherm.eigenvectorBasis i‖ = 1
    exact hTherm.eigenvectorBasis.orthonormal.1 i
  have heig : T *ᵥ z = theta • z := hTherm.mulVec_eigenvectorBasis i
  have hres : blockDiagonal H *ᵥ z - theta • z = (blockDiagonal H - T) *ᵥ z := by
    rw [Matrix.sub_mulVec, heig]
  have hbound : coordNorm (blockDiagonal H *ᵥ z - theta • z) ≤ ‖blockDiagonal H - T‖ := by
    rw [hres]
    have := coordNorm_mulVec_le (blockDiagonal H - T) z
    rwa [hz, mul_one] at this
  have hdist := spectralDistance_mul_coordNorm_le_blockResidual hn H hH theta z
  rw [hz, mul_one] at hdist
  exact hdist.trans hbound

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

theorem greenbaumTildeA_eigenvalue_localization (i : Fin (k + 1) × Fin n) :
    spectralDistance L.H
        ((indexed_isHermitian_of_transpose_eq L.greenbaumTildeA_transpose).eigenvalues i) ≤
      ‖L.greenbaumDelta‖ := by
  have h := block_eigenvalue_localization L.ambient_pos L.H L.hHsymm
    L.greenbaumTildeA L.greenbaumTildeA_transpose i
  rwa [show blockDiagonal L.H = L.greenbaumBlockOperator from rfl, ← norm_neg,
    neg_sub] at h

theorem greenbaumTildeA_eigenvalue_localization_explicit (i : Fin (k + 1) × Fin n) :
    spectralDistance L.H
        ((indexed_isHermitian_of_transpose_eq L.greenbaumTildeA_transpose).eigenvalues i) ≤
      (480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ :=
  (L.greenbaumTildeA_eigenvalue_localization i).trans L.greenbaumDelta_bound

end LanczosRun
end FinitePrecisionLanczos
