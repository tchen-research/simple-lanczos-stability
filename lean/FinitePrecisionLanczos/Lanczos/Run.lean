import FinitePrecisionLanczos.Core.Matrix

/-!
# Fixed finite-precision Lanczos run

This file is the formal counterpart of the five-line local panel
`eq:local-u`--`eq:local-normalize` in `finite_precision_lanczos.tex`.
Indices follow the paper's one-based convention: index `0` contains the
phantom values `v₀ = 0` and `β₀ = 0`, while a completed step is written
`j+1`.  The structure records exactly the identities and inequalities used
by the analysis; it does not model machine execution.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

/-- A completed `k`-step run satisfying the arithmetic interface in the PDF.

Fields `h_u`--`h_be` are respectively `eq:local-u` through
`eq:local-normalize`; the adjacent fields are their error bounds. -/
structure LanczosRun (n k : ℕ) where
  H : Mat n n
  v : ℕ → Vec n
  u : ℕ → Vec n
  w : ℕ → Vec n
  z : ℕ → Vec n
  α : ℕ → ℝ
  β : ℕ → ℝ
  eu : ℕ → Vec n
  ew : ℕ → Vec n
  ez : ℕ → Vec n
  eα : ℕ → ℝ
  Δ : ℕ → Vec n
  ε : ℝ
  hHsymm : Hᵀ = H
  hε_nonneg : 0 ≤ ε
  hk_pos : 0 < k
  hsmall : (k : ℝ) * ε ≤ 1 / 100
  hv_zero : v 0 = 0
  hβ_zero : β 0 = 0
  h_u : ∀ j, j < k → u (j + 1) = H *ᵥ v (j + 1) + eu (j + 1)
  heu : ∀ j, j < k →
    vnorm (eu (j + 1)) ≤ ε * ‖H‖ * vnorm (v (j + 1))
  h_w : ∀ j, j < k →
    w (j + 1) = u (j + 1) - β j • v j + ew (j + 1)
  hew : ∀ j, j < k →
    vnorm (ew (j + 1)) ≤ ε * (vnorm (u (j + 1)) + |β j| * vnorm (v j))
  h_al : ∀ j, j < k →
    α (j + 1) = vdot (v (j + 1)) (w (j + 1)) + eα (j + 1)
  heal : ∀ j, j < k →
    |eα (j + 1)| ≤ ε * vnorm (v (j + 1)) * vnorm (w (j + 1))
  h_z : ∀ j, j < k →
    z (j + 1) = w (j + 1) - α (j + 1) • v (j + 1) + ez (j + 1)
  hez : ∀ j, j < k →
    vnorm (ez (j + 1)) ≤
      ε * (vnorm (w (j + 1)) + |α (j + 1)| * vnorm (v (j + 1)))
  h_be : ∀ j, j < k →
    β (j + 1) • v (j + 2) = z (j + 1) + Δ (j + 1)
  hΔ : ∀ j, j < k → vnorm (Δ (j + 1)) ≤ ε * vnorm (z (j + 1))
  hnear : ∀ j, 1 ≤ j → j ≤ k → |vnorm (v j) ^ 2 - 1| ≤ ε
  hnext : β k ≠ 0 → |vnorm (v (k + 1)) ^ 2 - 1| ≤ ε
  hβ_nonneg : ∀ j, j ≤ k → 0 ≤ β j
  hβ_internal : ∀ j, 1 ≤ j → j < k → 0 < β j

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- Recurrence residual `f_j` in `eq:derived-quantities`, defined exactly
as in the PDF.  Its expression as the negative sum of the four local kernel
errors is proved below rather than built into the definition. -/
def f (j : ℕ) : Vec n :=
  L.H *ᵥ L.v j - L.β (j - 1) • L.v (j - 1) - L.α j • L.v j -
    L.β j • L.v (j + 1)

/-- Near-normalization defect `g_j` in `eq:derived-quantities`. -/
def g (j : ℕ) : ℝ := vdot (L.v j) (L.v j) - 1

/-- Weighted adjacent product `p_j` in `eq:derived-quantities`. -/
def p (j : ℕ) : ℝ := vdot (L.v j) (L.β j • L.v (j + 1))

@[simp] lemma p_zero : L.p 0 = 0 := by simp [p, vdot, L.hβ_zero]

/-- Exact column recurrence underlying the block relation `eq:governing`. -/
theorem governing_column (j : ℕ) (_hj : j < k) :
    L.H *ᵥ L.v (j + 1)
      = L.β j • L.v j + L.α (j + 1) • L.v (j + 1)
        + L.β (j + 1) • L.v (j + 2) + L.f (j + 1) := by
  simp only [f, Nat.add_sub_cancel]
  abel

/-- Eliminating the five computed intermediates gives the local-error
identity used in the proof of `thm:local-errors`. -/
theorem recurrence_error_identity (j : ℕ) (hj : j < k) :
    L.f (j + 1) =
      -(L.eu (j + 1) + L.ew (j + 1) + L.ez (j + 1) + L.Δ (j + 1)) := by
  have h1 : L.H *ᵥ L.v (j + 1) = L.u (j + 1) - L.eu (j + 1) := by
    rw [L.h_u j hj]
    abel
  have h2 : L.u (j + 1) = L.β j • L.v j + L.w (j + 1) - L.ew (j + 1) := by
    rw [L.h_w j hj]
    abel
  have h3 : L.w (j + 1) =
      L.α (j + 1) • L.v (j + 1) + L.z (j + 1) - L.ez (j + 1) := by
    rw [L.h_z j hj]
    abel
  have h4 : L.z (j + 1) =
      L.β (j + 1) • L.v (j + 2) - L.Δ (j + 1) := by
    rw [L.h_be j hj]
    abel
  simp only [f, Nat.add_sub_cancel]
  rw [h1, h2, h3, h4]
  abel

/-- Exact cancellation used in the proof of `thm:local-errors`.

This is the unnumbered cancellation identity in the proof of
`thm:local-errors`.
In particular, the matrix--vector error `eᵘ_j` does not occur. -/
theorem local_product_identity (j : ℕ) (hj : j < k) :
    L.p (j + 1)
      = -L.eα (j + 1) - L.g (j + 1) * L.α (j + 1)
        + vdot (L.v (j + 1)) (L.ez (j + 1))
        + vdot (L.v (j + 1)) (L.Δ (j + 1)) := by
  have hzj : vdot (L.v (j + 1)) (L.z (j + 1))
      = -L.eα (j + 1) - L.g (j + 1) * L.α (j + 1)
        + vdot (L.v (j + 1)) (L.ez (j + 1)) := by
    rw [L.h_z j hj]
    simp only [vdot, dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul, g]
    have hal : L.v (j + 1) ⬝ᵥ L.w (j + 1)
        = L.α (j + 1) - L.eα (j + 1) := by
      rw [L.h_al j hj]
      simp only [vdot]
      ring
    rw [hal]
    ring
  rw [p, L.h_be j hj]
  rw [vdot, dotProduct_add]
  have hzj' : L.v (j + 1) ⬝ᵥ L.z (j + 1)
      = -L.eα (j + 1) - L.g (j + 1) * L.α (j + 1)
        + L.v (j + 1) ⬝ᵥ L.ez (j + 1) := by
    simpa only [vdot] using hzj
  rw [hzj']
  rfl

end LanczosRun
end FinitePrecisionLanczos
