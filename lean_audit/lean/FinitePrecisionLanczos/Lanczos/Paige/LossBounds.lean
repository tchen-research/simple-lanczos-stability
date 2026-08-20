import FinitePrecisionLanczos.Lanczos.Paige.Loss








namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator


lemma abs_apply_le_one_of_vdot_self {k : ℕ} (y : Vec k) (hy : vdot y y = 1)
    (j : Fin k) : |y j| ≤ 1 := by
  have hs := vnorm_sq y
  have hv0 := vnorm_nonneg y
  have hv : vnorm y = 1 := by
    rw [hy] at hs
    nlinarith
  simpa [hv] using abs_apply_le_vnorm y j


lemma abs_quadratic_le_card_sq {k : ℕ} (M : Mat k k) (y : Vec k) (B : ℝ)
    (hy : vdot y y = 1) (hB : 0 ≤ B) (hM : ∀ i j, |M i j| ≤ B) :
    |vdot y (M *ᵥ y)| ≤ (k : ℝ) ^ 2 * B := by
  have hyc : ∀ j : Fin k, |y j| ≤ 1 := abs_apply_le_one_of_vdot_self y hy
  simp only [vdot, dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  calc
    |∑ i : Fin k, ∑ j : Fin k, y i * (M i j * y j)|
        ≤ ∑ i : Fin k, |∑ j : Fin k, y i * (M i j * y j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin k, ∑ j : Fin k, |y i * (M i j * y j)| := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, ∑ _j : Fin k, B := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul, abs_mul]
          calc
            |y i| * (|M i j| * |y j|) ≤ 1 * (B * 1) := by
              exact mul_le_mul (hyc i)
                (mul_le_mul (hM i j) (hyc j) (abs_nonneg _) hB)
                (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
            _ = B := by ring
    _ = (k : ℝ) ^ 2 * B := by simp; ring

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)


lemma Tmat_entry_bound (i j : Fin k) :
    |L.Tmat i j| ≤ (300 * (k : ℝ)) * ‖L.H‖ := by
  have hci := L.coefficients (i.1 + 1) (by omega) (Nat.succ_le_iff.mpr i.2)
  have hcj := L.coefficients (j.1 + 1) (by omega) (Nat.succ_le_iff.mpr j.2)
  have hH := norm_nonneg L.H
  have hi : ((i.1 + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.succ_le_iff.mpr i.2
  have hj : ((j.1 + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.succ_le_iff.mpr j.2
  have ha : |L.α (i.1 + 1)| ≤ (100 * (k : ℝ)) * ‖L.H‖ := by
    calc
      |L.α (i.1 + 1)| ≤ (100 * ((i.1 + 1 : ℕ) : ℝ)) * ‖L.H‖ := hci.alpha
      _ ≤ (100 * (k : ℝ)) * ‖L.H‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by norm_num)) hH
  have hbi : L.β (i.1 + 1) ≤ (100 * (k : ℝ)) * ‖L.H‖ := by
    calc
      L.β (i.1 + 1) ≤ (100 * ((i.1 + 1 : ℕ) : ℝ)) * ‖L.H‖ := hci.beta
      _ ≤ (100 * (k : ℝ)) * ‖L.H‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by norm_num)) hH
  have hbj : L.β (j.1 + 1) ≤ (100 * (k : ℝ)) * ‖L.H‖ := by
    calc
      L.β (j.1 + 1) ≤ (100 * ((j.1 + 1 : ℕ) : ℝ)) * ‖L.H‖ := hcj.beta
      _ ≤ (100 * (k : ℝ)) * ‖L.H‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj (by norm_num)) hH
  let B := (100 * (k : ℝ)) * ‖L.H‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h1 : |if i = j then L.α (i.1 + 1) else 0| ≤ B := by
    by_cases h : i = j
    · rw [if_pos h]
      exact ha
    · simp [h, hB]
  have h2 : |if i.1 + 1 = j.1 then L.β (i.1 + 1) else 0| ≤ B := by
    by_cases h : i.1 + 1 = j.1
    · rw [if_pos h, abs_of_nonneg (L.hβ_nonneg _ (Nat.succ_le_iff.mpr i.2))]
      exact hbi
    · simp [h, hB]
  have h3 : |if j.1 + 1 = i.1 then L.β (j.1 + 1) else 0| ≤ B := by
    by_cases h : j.1 + 1 = i.1
    · rw [if_pos h, abs_of_nonneg (L.hβ_nonneg _ (Nat.succ_le_iff.mpr j.2))]
      exact hbj
    · simp [h, hB]
  rw [Tmat]
  calc
    |(if i = j then L.α (i.1 + 1) else 0)
        + (if i.1 + 1 = j.1 then L.β (i.1 + 1) else 0)
        + (if j.1 + 1 = i.1 then L.β (j.1 + 1) else 0)|
      ≤ |if i = j then L.α (i.1 + 1) else 0|
          + |if i.1 + 1 = j.1 then L.β (i.1 + 1) else 0|
          + |if j.1 + 1 = i.1 then L.β (j.1 + 1) else 0| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ B + B + B := by gcongr
    _ = (300 * (k : ℝ)) * ‖L.H‖ := by simp [B]; ring


lemma Qmat_entry (i j : Fin k) :
    L.Qmat i j = L.Tmat i j * (L.g (j.1 + 1) - L.g (i.1 + 1)) := by
  simp [Qmat, Dmat, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring


lemma Qmat_entry_bound (i j : Fin k) :
    |L.Qmat i j| ≤ (600 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  have hgi := L.abs_g_le (i.1 + 1) (by omega) (Nat.succ_le_iff.mpr i.2)
  have hgj := L.abs_g_le (j.1 + 1) (by omega) (Nat.succ_le_iff.mpr j.2)
  have hdiff : |L.g (j.1 + 1) - L.g (i.1 + 1)| ≤ 2 * L.ε := by
    calc
      |L.g (j.1 + 1) - L.g (i.1 + 1)|
          ≤ |L.g (j.1 + 1)| + |L.g (i.1 + 1)| := by
            simpa using abs_sub_le (L.g (j.1 + 1)) 0 (L.g (i.1 + 1))
      _ ≤ L.ε + L.ε := add_le_add hgj hgi
      _ = 2 * L.ε := by ring
  rw [L.Qmat_entry, abs_mul]
  calc
      |L.Tmat i j| * |L.g (j.1 + 1) - L.g (i.1 + 1)|
        ≤ ((300 * (k : ℝ)) * ‖L.H‖) * (2 * L.ε) :=
          mul_le_mul (L.Tmat_entry_bound i j) hdiff (abs_nonneg _)
            (mul_nonneg (by positivity) (norm_nonneg _))
    _ = (600 * (k : ℝ)) * L.ε * ‖L.H‖ := by ring


lemma upQ_entry_bound (i j : Fin k) :
    |L.upQ i j| ≤ (600 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  by_cases hij : i.1 < j.1
  · simpa [upQ, hij] using L.Qmat_entry_bound i j
  · rw [upQ, if_neg hij, abs_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg k)) L.hε_nonneg)
      (norm_nonneg _)



theorem eta_bound (y : Vec k) (hy : vdot y y = 1) :
    |L.eta y| ≤ (3400 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by
  let BG := (2800 * (k : ℝ)) * L.ε * ‖L.H‖
  let BQ := (600 * (k : ℝ)) * L.ε * ‖L.H‖
  have hBG : 0 ≤ BG := by
    dsimp [BG]
    exact mul_nonneg (mul_nonneg (by positivity) L.hε_nonneg) (norm_nonneg _)
  have hBQ : 0 ≤ BQ := by
    dsimp [BQ]
    exact mul_nonneg (mul_nonneg (by positivity) L.hε_nonneg) (norm_nonneg _)
  have hupG : ∀ i j, |L.upG i j| ≤ BG := by
    intro i j
    by_cases hij : i.1 < j.1
    · simpa [upG, hij, BG] using L.Gmat_entry_bound i j
    · simp [upG, hij, hBG]
  have hupQ : ∀ i j, |L.upQ i j| ≤ BQ := by
    intro i j
    by_cases hij : i.1 < j.1
    · simpa [upQ, hij, BQ] using L.Qmat_entry_bound i j
    · simp [upQ, hij, hBQ]
  have hG := abs_quadratic_le_card_sq L.upG y BG hy hBG hupG
  have hQ := abs_quadratic_le_card_sq L.upQ y BQ hy hBQ hupQ
  rw [eta]
  calc
    |-vdot y (L.upG *ᵥ y) + vdot y (L.upQ *ᵥ y)|
        ≤ |vdot y (L.upG *ᵥ y)| + |vdot y (L.upQ *ᵥ y)| := by
          simpa using abs_add_le (-vdot y (L.upG *ᵥ y)) (vdot y (L.upQ *ᵥ y))
    _ ≤ (k : ℝ) ^ 2 * BG + (k : ℝ) ^ 2 * BQ := add_le_add hG hQ
    _ = (3400 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by simp [BG, BQ]; ring


lemma p_bound_all (j : ℕ) (hjk : j ≤ k) :
    |L.p j| ≤ (1200 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  by_cases hj0 : j = 0
  · subst j
    rw [L.p_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by positivity) L.hε_nonneg) (norm_nonneg _)
  · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have hp := L.local_product_bound j hj1 hjk
    have hjr : (j : ℝ) ≤ k := by exact_mod_cast hjk
    have hs : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
    nlinarith



lemma paigeSum_bound (y : Vec k) (hy : vdot y y = 1) :
    |L.paigeSum y| ≤ (2400 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖ := by
  have hyc : ∀ j : Fin k, |y j| ≤ 1 := abs_apply_le_one_of_vdot_self y hy
  let B := (1200 * (k : ℝ)) * L.ε * ‖L.H‖
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (by positivity) L.hε_nonneg) (norm_nonneg _)
  have hdiff : ∀ j : Fin k, |L.p (j.1 + 1) - L.p j.1| ≤ 2 * B := by
    intro j
    have h1 := L.p_bound_all (j.1 + 1) (Nat.succ_le_iff.mpr j.2)
    have h0 := L.p_bound_all j.1 (Nat.le_of_lt j.2)
    calc
      |L.p (j.1 + 1) - L.p j.1| ≤ |L.p (j.1 + 1)| + |L.p j.1| := by
        simpa using abs_sub_le (L.p (j.1 + 1)) 0 (L.p j.1)
      _ ≤ B + B := by simpa [B] using add_le_add h1 h0
      _ = 2 * B := by ring
  rw [paigeSum]
  calc
    |∑ j : Fin k, (y j) ^ 2 * (L.p (j.1 + 1) - L.p j.1)|
        ≤ ∑ j : Fin k, |(y j) ^ 2 * (L.p (j.1 + 1) - L.p j.1)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, 2 * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_pow]
      have hy2 : |y j| ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg (abs_nonneg (y j)) (sub_nonneg.mpr (hyc j))]
      calc
        |y j| ^ 2 * |L.p (j.1 + 1) - L.p j.1|
            ≤ 1 * (2 * B) := mul_le_mul hy2 (hdiff j) (abs_nonneg _) (by norm_num)
        _ = 2 * B := one_mul _
    _ = (2400 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖ := by simp [B]; ring


theorem paige_bound (y : Vec k) (theta : ℝ) (hy : vdot y y = 1)
    (heig : L.Tmat *ᵥ y = theta • y) :
    |vdot (L.ritzVector y) L.rawBoundary * y (lastIndex L.hk_pos)|
      ≤ (6000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by
  rw [L.paige_identity y theta heig]
  have hsum := L.paigeSum_bound y hy
  have heta := L.eta_bound y hy
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have hs : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
  calc
    |L.paigeSum y + L.eta y| ≤ |L.paigeSum y| + |L.eta y| := abs_add_le _ _
    _ ≤ (2400 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖
          + (3400 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := add_le_add hsum heta
    _ ≤ (6000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by
      have hk23 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by nlinarith [sq_nonneg (k : ℝ)]
      nlinarith

end LanczosRun
end FinitePrecisionLanczos
