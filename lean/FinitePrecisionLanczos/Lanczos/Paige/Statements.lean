import FinitePrecisionLanczos.Lanczos.Paige.Stabilized

/-!
# Statements matching the revised Paige section

This file gathers the conclusions that the PDF now presents as bundled
theorems.  The underlying proofs remain split into small lemmas, while these
records expose the exact explicit-constant counterparts of the displayed
statements for line-by-line auditing.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- Explicit-constant form of all conclusions bundled into
`lem:gram-commutator`. -/
structure GramCommutatorConclusion : Prop where
  commutator :
    L.Tmat * L.Omega - L.Omega * L.Tmat =
      L.Cmat - L.Cmatᵀ + L.Gmat
  G_entry_bound : ∀ r s : Fin k,
    |L.Gmat r s| ≤ (2800 * (k : ℝ)) * L.ε * ‖L.H‖
  upper_commutator :
    L.Tmat * L.Rmat - L.Rmat * L.Tmat =
      L.Cmat + L.Nmat + L.upG - L.upQ
  diagonal_term_support : ∀ i j : Fin k,
    i.1 + 1 ≠ j.1 → L.upQ i j = 0
  diagonal_term_bound : ∀ i j : Fin k,
    |L.upQ i j| ≤ (600 * (k : ℝ)) * L.ε * ‖L.H‖

/-- `lem:gram-commutator`, in the same order as the assertions in the PDF. -/
theorem gram_commutator_conclusion : L.GramCommutatorConclusion := by
  exact {
    commutator := L.gram_commutator
    G_entry_bound := L.Gmat_entry_bound
    upper_commutator := L.upper_commutator
    diagonal_term_support := L.upQ_eq_zero_of_not_first_superdiagonal
    diagonal_term_bound := L.upQ_entry_bound
  }

end LanczosRun
end FinitePrecisionLanczos
