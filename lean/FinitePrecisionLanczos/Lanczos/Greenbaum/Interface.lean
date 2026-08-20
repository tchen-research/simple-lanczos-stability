import FinitePrecisionLanczos.Lanczos.Paige.Stabilized

/-!
# Internal unnormalized defect estimates

These estimates support the internal change-of-coordinates proof.  The
current PDF presents their normalized consequences directly in
`lem:normalized-errors`.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- The maximum raw weighted adjacent product, with value zero
when `k=1`. -/
noncomputable def adjacentDefect : ℝ :=
  if hk : 1 < k then
    Finset.univ.sup'
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (by omega : 0 < k - 1)))
      (fun j : Fin (k - 1) =>
        L.β (j.1 + 1) * |vdot (L.v (j.1 + 1)) (L.v (j.1 + 2))|)
  else 0

/-- Dimensionally consistent raw Paige defect used internally. -/
noncomputable def paigeDefect : ℝ :=
  ‖L.Fmat‖ + ‖L.H‖ * ‖L.Dmat‖ + L.adjacentDefect +
    |vdot (L.v k) L.rawBoundary|

/-- The unnormalized governing recurrence for the run. -/
theorem deterministic_interface :
    L.H * L.Vmat = L.Vmat * L.Tmat + L.boundary + L.Fmat :=
  L.governing_matrix

/-- Operator norm of the diagonal Gram defect. -/
lemma Dmat_norm_bound : ‖L.Dmat‖ ≤ L.ε := by
  rw [Dmat, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg L.hε_nonneg).2
  intro j
  simpa [Real.norm_eq_abs] using
    L.abs_g_le (j.1 + 1) (by omega) (Nat.succ_le_iff.mpr j.2)

lemma Dmat_norm_le_quarter : ‖L.Dmat‖ ≤ 1 / 4 := by
  exact L.Dmat_norm_bound.trans
    (L.epsilon_le_one_hundredth.trans (by norm_num))

/-- Maximum adjacent-product term in the Paige defect. -/
lemma adjacentDefect_bound :
    L.adjacentDefect ≤ (1200 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  unfold adjacentDefect
  split_ifs with hk
  · rw [Finset.sup'_le_iff]
    intro j _hj
    have hp := L.local_product_bound (j.1 + 1) (by omega)
      (by have := j.2; omega)
    have hb : 0 ≤ L.β (j.1 + 1) := L.hβ_nonneg _ (by omega)
    have hjk : (((j.1 + 1 : ℕ) : ℝ)) ≤ k := by
      exact_mod_cast (show j.1 + 1 ≤ k by omega)
    have hscale : 0 ≤ L.ε * ‖L.H‖ :=
      mul_nonneg L.hε_nonneg (norm_nonneg _)
    have hp' : L.β (j.1 + 1) *
        |vdot (L.v (j.1 + 1)) (L.v (j.1 + 2))| ≤
          (1200 * (((j.1 + 1 : ℕ) : ℝ))) * L.ε * ‖L.H‖ := by
      simpa [p, vdot, dotProduct_smul, smul_eq_mul, abs_mul,
        abs_of_nonneg hb, mul_assoc] using hp
    calc
      L.β (j.1 + 1) * |vdot (L.v (j.1 + 1)) (L.v (j.1 + 2))|
          ≤ (1200 * (((j.1 + 1 : ℕ) : ℝ))) * L.ε * ‖L.H‖ := hp'
      _ ≤ (1200 * (k : ℝ)) * L.ε * ‖L.H‖ := by
        nlinarith
  · have hscale : 0 ≤ (1200 * (k : ℝ)) * L.ε * ‖L.H‖ :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) L.hε_nonneg)
        (norm_nonneg _)
    exact hscale

/-- Last raw weighted product. -/
lemma boundaryDefect_bound :
    |vdot (L.v k) L.rawBoundary| ≤
      (1200 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  have hp := L.local_product_bound k L.hk_pos le_rfl
  simpa [rawBoundary, p, vdot, dotProduct_smul, smul_eq_mul,
    abs_mul, mul_assoc, mul_left_comm, mul_comm] using hp

/-- Crude coefficient bound converted to the operator norm required by the
Greenbaum interface. -/
lemma Tmat_norm_bound : ‖L.Tmat‖ ≤ (300 * (k : ℝ) ^ 3) * ‖L.H‖ := by
  have hentry := norm_le_card_mul_card_mul_of_entry_bound L.Tmat
    ((300 * (k : ℝ)) * ‖L.H‖) (by positivity) L.Tmat_entry_bound
  calc
    ‖L.Tmat‖ ≤ (k : ℝ) * (k : ℝ) * ((300 * (k : ℝ)) * ‖L.H‖) := hentry
    _ = (300 * (k : ℝ) ^ 3) * ‖L.H‖ := by ring

/-- A single explicit polynomial bound for the raw Paige defect. -/
theorem paigeDefect_bound :
    L.paigeDefect ≤ (4000 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖ := by
  have hF := L.Fmat_bound
  have hD := L.Dmat_norm_bound
  have hA := L.adjacentDefect_bound
  have hB := L.boundaryDefect_bound
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hkSq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hscale : 0 ≤ L.ε * ‖L.H‖ :=
    mul_nonneg L.hε_nonneg (norm_nonneg _)
  have hD' : ‖L.H‖ * ‖L.Dmat‖ ≤ L.ε * ‖L.H‖ := by
    nlinarith [norm_nonneg L.H]
  have hlin : (k : ℝ) * (L.ε * ‖L.H‖) ≤
      (k : ℝ) ^ 2 * (L.ε * ‖L.H‖) :=
    mul_le_mul_of_nonneg_right hkSq hscale
  unfold paigeDefect
  ring_nf at hF hA hB ⊢
  nlinarith

end LanczosRun
end FinitePrecisionLanczos
