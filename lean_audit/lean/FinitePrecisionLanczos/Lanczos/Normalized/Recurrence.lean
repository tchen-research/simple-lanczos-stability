import FinitePrecisionLanczos.Lanczos.Normalized.Normalization
import FinitePrecisionLanczos.Core.GramCommutator


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

noncomputable def normalizedF (j : ℕ) : Vec n :=
  L.H *ᵥ L.normalizedVec j - L.β (j - 1) • L.normalizedVec (j - 1) -
    L.α j • L.normalizedVec j - L.β j • L.normalizedVec (j + 1)

noncomputable def normalizedP (j : ℕ) : ℝ :=
  vdot (L.normalizedVec j) (L.β j • L.normalizedVec (j + 1))

noncomputable def normalizedFmat : Mat n k :=
  ofCols fun j => L.normalizedF (j.1 + 1)

theorem normalized_governing :
    L.H * L.normalizedV =
      L.normalizedV * L.Tmat +
        L.β k • lastOuter L.hk_pos L.normalizedVNext + L.normalizedFmat := by
  rw [L.normalizedV_eq_ofCols, L.ofCols_mul_Tmat]
  ext a j
  have hcol : L.H *ᵥ L.normalizedVec (j.1 + 1) =
      L.β j.1 • L.normalizedVec j.1 + L.α (j.1 + 1) • L.normalizedVec (j.1 + 1) +
        L.β (j.1 + 1) • L.normalizedVec (j.1 + 1 + 1) +
        L.normalizedF (j.1 + 1) := by
    simp only [normalizedF, Nat.add_sub_cancel]
    abel
  change (L.H *ᵥ L.normalizedVec (j.1 + 1)) a = _
  rw [hcol]
  simp only [Matrix.add_apply, Matrix.smul_apply, lastOuter_apply, ofCols,
    normalizedFmat, normalizedVNext, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j.1 + 1 < k
  · simp [hj, show ¬j.1 + 1 = k by omega]
  · have hj' : j.1 + 1 = k := by omega
    simp only [hj']
    rw [show j.1 + 2 = k + 1 by omega]
    simp

theorem normalized_governing_succ :
    L.H * L.normalizedV = L.normalizedVsucc * L.underlineTmat + L.normalizedFmat := by
  rw [underlineTmat, mul_underlineT L.hk_pos, leadCols_normalizedVsucc,
    lastCol_normalizedVsucc]
  exact L.normalized_governing

theorem normalizedF_sub_identity {j : ℕ} (hj : j ≤ k) :
    L.normalizedF j - (L.normScale j)⁻¹ • L.f j =
      ((L.normScale j)⁻¹ - (L.normScale (j - 1))⁻¹) •
          (L.β (j - 1) • L.v (j - 1)) +
        ((L.normScale j)⁻¹ - (L.normScale (j + 1))⁻¹) •
          (L.β j • L.v (j + 1)) := by
  have h1 := L.beta_smul_normalizedVec (show j - 1 ≤ k by omega)
  have h2 := L.beta_smul_normalizedVec_succ hj
  have h3 : L.normalizedVec j = (L.normScale j)⁻¹ • L.v j := by
    rw [L.normalizedVec_of_le hj, L.normScale_of_le hj]
  simp only [normalizedF, f]
  rw [h1, h2, h3, Matrix.mulVec_smul]
  module

theorem normalizedP_identity {j : ℕ} (hj : j ≤ k) :
    L.normalizedP j = (L.normScale j)⁻¹ * (L.normScale (j + 1))⁻¹ * L.p j := by
  have h3 : L.normalizedVec j = (L.normScale j)⁻¹ • L.v j := by
    rw [L.normalizedVec_of_le hj, L.normScale_of_le hj]
  rw [normalizedP, L.beta_smul_normalizedVec_succ hj, h3, p]
  simp only [vdot, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

end LanczosRun
end FinitePrecisionLanczos
