import FinitePrecisionLanczos.Core.DilationBounds
import FinitePrecisionLanczos.Lanczos.Ritz


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

noncomputable def columnNorm (j : Fin k) : ℝ := vnorm (L.v (j.1 + 1))

noncomputable def invNormDiag : Mat k k :=
  Matrix.diagonal fun j => (L.columnNorm j)⁻¹

noncomputable def normalizedV : Mat n k := L.Vmat * L.invNormDiag

lemma columnNorm_sq_bounds (j : Fin k) :
    1 - L.ε ≤ L.columnNorm j ^ 2 ∧ L.columnNorm j ^ 2 ≤ 1 + L.ε :=
  L.near_unit_sq (by omega) (Nat.succ_le_iff.mpr j.2)

lemma columnNorm_lower (j : Fin k) : 1 - L.ε ≤ L.columnNorm j := by
  have hs := (L.columnNorm_sq_bounds j).1
  have hd := vnorm_nonneg (L.v (j.1 + 1))
  have he0 := L.hε_nonneg
  have he1 := L.epsilon_le_one
  have hone : 0 < 1 - L.ε := by
    linarith [L.epsilon_le_one_hundredth]
  by_contra h
  have hlt : L.columnNorm j < 1 - L.ε := lt_of_not_ge h
  have hsum : 0 < (1 - L.ε) + L.columnNorm j :=
    add_pos_of_pos_of_nonneg hone hd
  have hprod : 0 < ((1 - L.ε) - L.columnNorm j) *
      ((1 - L.ε) + L.columnNorm j) :=
    mul_pos (sub_pos.mpr hlt) hsum
  have hsq_lt : L.columnNorm j ^ 2 < (1 - L.ε) ^ 2 := by
    nlinarith
  have hsq_le : (1 - L.ε) ^ 2 ≤ 1 - L.ε := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr he1)]
  linarith

lemma columnNorm_pos (j : Fin k) : 0 < L.columnNorm j := by
  have hl := L.columnNorm_lower j
  have he := L.epsilon_le_one_hundredth
  linarith

lemma columnNorm_ne_zero (j : Fin k) : L.columnNorm j ≠ 0 :=
  ne_of_gt (L.columnNorm_pos j)

lemma invColumnNorm_nonneg (j : Fin k) : 0 ≤ (L.columnNorm j)⁻¹ :=
  (L.columnNorm_pos j).le |> inv_nonneg.mpr

lemma normalizedV_apply (i : Fin n) (j : Fin k) :
    L.normalizedV i j = (L.columnNorm j)⁻¹ * L.v (j.1 + 1) i := by
  simp [normalizedV, Vmat, invNormDiag, Matrix.mul_diagonal, mul_comm]

lemma normalizedV_column (j : Fin k) :
    (fun i => L.normalizedV i j) = (L.columnNorm j)⁻¹ • L.v (j.1 + 1) := by
  ext i
  simp [L.normalizedV_apply, Pi.smul_apply]

theorem normalizedV_unit (j : Fin k) :
    vnorm (fun i => L.normalizedV i j) = 1 := by
  rw [L.normalizedV_column, vnorm_smul]
  rw [abs_of_nonneg (L.invColumnNorm_nonneg j)]
  dsimp [columnNorm]
  exact inv_mul_cancel₀ (L.columnNorm_ne_zero j)

/-- Unit columns give the paper's √k bound, even after loss of orthogonality. -/
lemma normalizedV_norm_sqrt : ‖L.normalizedV‖ ≤ Real.sqrt (k : ℝ) := by
  have h := norm_ofCols_le_sqrt_card (fun j : Fin k => fun i => L.normalizedV i j)
    1 (by norm_num) (fun j => (L.normalizedV_unit j).le)
  change ‖L.normalizedV‖ ≤ Real.sqrt (k : ℝ) * 1 at h
  simpa only [mul_one] using h

lemma normalizedV_norm : ‖L.normalizedV‖ ≤ (k : ℝ) := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have hs : Real.sqrt (k : ℝ) ≤ k := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg k), Real.sqrt_nonneg (k : ℝ)]
  exact L.normalizedV_norm_sqrt.trans hs

noncomputable def normalizedR : Mat k k := fun i j =>
  if i.1 < j.1 then (L.normalizedVᵀ * L.normalizedV) i j else 0

lemma normalizedR_strictUpper : StrictUpper L.normalizedR := by
  intro i j hij
  simp [normalizedR, hij]

lemma normalizedGram_diag (j : Fin k) :
    (L.normalizedVᵀ * L.normalizedV) j j = 1 := by
  have hsq := vnorm_sq (fun i => L.normalizedV i j)
  rw [L.normalizedV_unit] at hsq
  simpa [Matrix.mul_apply, vdot, dotProduct] using hsq.symm

theorem normalized_gram_split :
    L.normalizedVᵀ * L.normalizedV = 1 + L.normalizedRᵀ + L.normalizedR := by
  ext i j
  rcases lt_trichotomy i.1 j.1 with hij | hij | hij
  · have hne : i ≠ j := by intro h; subst j; omega
    simp [normalizedR, hij, not_lt_of_ge hij.le, hne]
  · have heq : i = j := Fin.ext hij
    subst j
    simp [normalizedR, L.normalizedGram_diag]
  · have hji : j.1 < i.1 := hij
    have hne : i ≠ j := by intro h; subst j; omega
    have hsym : (L.normalizedVᵀ * L.normalizedV) j i =
        (L.normalizedVᵀ * L.normalizedV) i j := by
      simp [Matrix.mul_apply]
      exact dotProduct_comm _ _
    simp [normalizedR, hji, not_lt_of_ge hji.le, hne, hsym]


lemma inv_near_one_of_sq {ε d : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100)
    (hd : 0 ≤ d) (h : |d ^ 2 - 1| ≤ ε) :
    0 < d ∧ |d - 1| ≤ ε ∧ |d⁻¹ - 1| ≤ 2 * ε := by
  have h' := abs_le.mp h
  have hd1 : |d - 1| ≤ ε := by
    have hfac : d ^ 2 - 1 = (d - 1) * (d + 1) := by ring
    have hpos : 1 ≤ d + 1 := by linarith
    rw [hfac, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < d + 1)] at h
    calc
      |d - 1| = |d - 1| * 1 := by ring
      _ ≤ |d - 1| * (d + 1) := mul_le_mul_of_nonneg_left hpos (abs_nonneg _)
      _ ≤ ε := h
  have hlo : 1 - ε ≤ d := by linarith [(abs_le.mp hd1).1]
  have hdpos : 0 < d := by linarith
  refine ⟨hdpos, hd1, ?_⟩
  have hrepr : d⁻¹ - 1 = (1 - d) / d := by field_simp
  rw [hrepr, abs_div, abs_of_pos hdpos, abs_sub_comm, div_le_iff₀ hdpos]
  nlinarith

noncomputable def normScale (j : ℕ) : ℝ :=
  if j = k + 1 ∧ L.β k = 0 then 1 else vnorm (L.v j)

noncomputable def normalizedVec (j : ℕ) : Vec n :=
  if j = k + 1 ∧ L.β k = 0 then (vnorm (L.v 1))⁻¹ • L.v 1
  else (L.normScale j)⁻¹ • L.v j

noncomputable def normalizedVNext : Vec n := L.normalizedVec (k + 1)

lemma normScale_of_le {j : ℕ} (hj : j ≤ k) : L.normScale j = vnorm (L.v j) := by
  simp [normScale, show j ≠ k + 1 by omega]

lemma normalizedVec_of_le {j : ℕ} (hj : j ≤ k) :
    L.normalizedVec j = (vnorm (L.v j))⁻¹ • L.v j := by
  simp [normalizedVec, show j ≠ k + 1 by omega, L.normScale_of_le hj]

lemma normScale_nonneg (j : ℕ) : 0 ≤ L.normScale j := by
  unfold normScale
  split_ifs
  · exact zero_le_one
  · exact vnorm_nonneg _

lemma normScale_bounds {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ k + 1) :
    0 < L.normScale j ∧ |(L.normScale j)⁻¹ - 1| ≤ 2 * L.ε := by
  have he0 := L.hε_nonneg
  have he := L.epsilon_le_one_hundredth
  by_cases hjk : j ≤ k
  · rw [L.normScale_of_le hjk]
    have h := inv_near_one_of_sq he0 he (vnorm_nonneg (L.v j))
      (L.hnear j hj1 hjk)
    exact ⟨h.1, h.2.2⟩
  · have hj' : j = k + 1 := by omega
    subst hj'
    by_cases hb : L.β k = 0
    · simp [normScale, hb, he0]
    · rw [normScale, if_neg (by tauto)]
      have h := inv_near_one_of_sq he0 he (vnorm_nonneg (L.v (k + 1)))
        (L.hnext hb)
      exact ⟨h.1, h.2.2⟩

/-- The bounds on d_j printed in the normalized-local-errors proof. -/
theorem normScale_near_one {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ k + 1) :
    1 / 2 ≤ L.normScale j ∧ |L.normScale j - 1| ≤ L.ε := by
  have he := L.epsilon_le_one_hundredth
  by_cases ht : j = k + 1 ∧ L.β k = 0
  · norm_num [normScale, ht, L.hε_nonneg]
  · have hsq : |vnorm (L.v j) ^ 2 - 1| ≤ L.ε := by
      by_cases hjk : j ≤ k
      · exact L.hnear j hj1 hjk
      · have hj' : j = k + 1 := by omega
        subst j
        exact L.hnext (by tauto)
    have h := inv_near_one_of_sq L.hε_nonneg he (vnorm_nonneg _) hsq
    rw [normScale, if_neg ht]
    exact ⟨by linarith [(abs_le.mp h.2.1).1], h.2.1⟩

lemma normScale_inv_le_two {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ k + 1) :
    (L.normScale j)⁻¹ ≤ 2 := by
  have h := abs_le.mp (L.normScale_bounds hj1 hj).2
  linarith [L.epsilon_le_one_hundredth]

lemma normScale_inv_sub {i j : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ k + 1)
    (hj1 : 1 ≤ j) (hj : j ≤ k + 1) :
    |(L.normScale i)⁻¹ - (L.normScale j)⁻¹| ≤ 4 * L.ε := by
  have h1 := (L.normScale_bounds hi1 hi).2
  have h2 := (L.normScale_bounds hj1 hj).2
  calc
    |(L.normScale i)⁻¹ - (L.normScale j)⁻¹| =
        |((L.normScale i)⁻¹ - 1) - ((L.normScale j)⁻¹ - 1)| := by ring_nf
    _ ≤ |(L.normScale i)⁻¹ - 1| + |(L.normScale j)⁻¹ - 1| := abs_sub _ _
    _ ≤ 4 * L.ε := by linarith

theorem normalizedVec_unit {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ k + 1) :
    vnorm (L.normalizedVec j) = 1 := by
  have hunit : ∀ i, 1 ≤ i → i ≤ k + 1 → ¬(i = k + 1 ∧ L.β k = 0) →
      vnorm ((L.normScale i)⁻¹ • L.v i) = 1 := by
    intro i hi1 hi hne
    have hpos := (L.normScale_bounds hi1 hi).1
    rw [vnorm_smul, abs_of_nonneg (inv_nonneg.mpr hpos.le)]
    have hs : L.normScale i = vnorm (L.v i) := by simp [normScale, hne]
    rw [← hs]
    exact inv_mul_cancel₀ hpos.ne'
  unfold normalizedVec
  split_ifs with hterm
  · have h1 := hunit 1 le_rfl (by omega)
      (by intro h; have := L.hk_pos; omega)
    simpa [L.normScale_of_le (show 1 ≤ k from L.hk_pos)] using h1
  · exact hunit j hj1 hj hterm

lemma beta_smul_normalizedVec {j : ℕ} (hj : j ≤ k) :
    L.β j • L.normalizedVec j = (L.normScale j)⁻¹ • (L.β j • L.v j) := by
  rw [L.normalizedVec_of_le hj, L.normScale_of_le hj, smul_comm]

lemma beta_smul_normalizedVec_succ {j : ℕ} (hj : j ≤ k) :
    L.β j • L.normalizedVec (j + 1) =
      (L.normScale (j + 1))⁻¹ • (L.β j • L.v (j + 1)) := by
  by_cases hterm : j + 1 = k + 1 ∧ L.β k = 0
  · have hj' : j = k := by omega
    subst hj'
    simp [hterm.2]
  · simp only [normalizedVec, if_neg hterm]
    rw [smul_comm]

lemma normalizedV_column_eq (j : Fin k) :
    (fun i => L.normalizedV i j) = L.normalizedVec (j.1 + 1) := by
  rw [L.normalizedV_column, L.normalizedVec_of_le (Nat.succ_le_iff.mpr j.2)]
  rfl

lemma normalizedV_eq_ofCols :
    L.normalizedV = ofCols fun j : Fin k => L.normalizedVec (j.1 + 1) := by
  ext i j
  have h := congrFun (L.normalizedV_column_eq j) i
  exact h


noncomputable def normalizedVsucc : Mat n (k + 1) := ofCols fun j => L.normalizedVec (j.1 + 1)

@[simp] lemma leadCols_normalizedVsucc : leadCols L.normalizedVsucc = L.normalizedV := by
  rw [L.normalizedV_eq_ofCols]
  rfl

@[simp] lemma lastCol_normalizedVsucc : lastCol L.normalizedVsucc = L.normalizedVNext := rfl

lemma normalizedVsucc_unit (j : Fin (k + 1)) :
    vnorm (fun i => L.normalizedVsucc i j) = 1 :=
  L.normalizedVec_unit (by omega) (by omega)

end LanczosRun
end FinitePrecisionLanczos
