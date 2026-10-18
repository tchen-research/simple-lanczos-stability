import FinitePrecisionLanczos.Lanczos.ComputedCommutator
import FinitePrecisionLanczos.Core.Commutator


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

lemma computedBoundaryTerm_quadratic (y : Vec k) :
    vdot y (lastOuter L.hk_pos (L.Vmatᵀ *ᵥ L.rawBoundary) *ᵥ y) =
      vdot (L.ritzVector y) L.rawBoundary * y (lastIndex L.hk_pos) := by
  have hy : vdot y (L.Vmatᵀ *ᵥ L.rawBoundary) =
      vdot (L.ritzVector y) L.rawBoundary := by
    simp only [vdot, ritzVector, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [lastOuter_mulVec]
  simp only [vdot, dotProduct_smul, smul_eq_mul] at hy ⊢
  rw [hy]
  simp only [lastIndex]
  ring

theorem computed_paige_identity (y : Vec k) (theta : ℝ)
    (heig : L.Tmat *ᵥ y = theta • y) :
    vdot (L.ritzVector y) L.rawBoundary * y (lastIndex L.hk_pos) =
      -vdot y (L.computedCommutator *ᵥ y) := by
  have hupper : L.Tmat * L.computedR - L.computedR * L.Tmat =
      lastOuter L.hk_pos (L.Vmatᵀ *ᵥ L.rawBoundary) +
        L.computedCommutator + 0 := by
    rw [computedCommutator_eq_rawBoundary]
    abel
  have hs := Core.paige_sandwich L.Tmat L.computedR
    (lastOuter L.hk_pos (L.Vmatᵀ *ᵥ L.rawBoundary))
    L.computedCommutator 0 L.Tmat_transpose y theta heig hupper
  rw [← L.computedBoundaryTerm_quadratic y]
  simpa [vdot] using hs

theorem paige_bound (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y) :
    |vdot (L.ritzVector y) L.rawBoundary * y (lastIndex L.hk_pos)| ≤
      (3000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by
  rw [L.computed_paige_identity y theta heig, abs_neg]
  exact (abs_quadratic_le_opNorm _ y hy).trans L.computedCommutator_bound

end LanczosRun
end FinitePrecisionLanczos
