import FinitePrecisionLanczos.Lanczos.Normalized.Recurrence


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

lemma vnorm_beta_smul_v_le {i : ℕ} (hi : i ≤ k) :
    vnorm (L.β i • L.v i) ≤ (8 * (k : ℝ)) * ‖L.H‖ := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    simp [L.hβ_zero]
    positivity
  · rw [vnorm_smul, abs_of_nonneg (L.hβ_nonneg i hi)]
    have hb := L.beta_bound i hi
    have hv := L.vnorm_v_le_two hpos hi
    have hik : (i : ℝ) ≤ k := by exact_mod_cast hi
    have hH := norm_nonneg L.H
    calc
      L.β i * vnorm (L.v i) ≤ ((4 * (k : ℝ)) * ‖L.H‖) * 2 :=
        mul_le_mul (hb.trans (by nlinarith)) hv (vnorm_nonneg _) (by positivity)
      _ = (8 * (k : ℝ)) * ‖L.H‖ := by ring

lemma vnorm_beta_smul_v_succ_le {i : ℕ} (hi : i ≤ k) :
    vnorm (L.β i • L.v (i + 1)) ≤ (8 * (k : ℝ)) * ‖L.H‖ := by
  have hH := norm_nonneg L.H
  have hb := L.beta_bound i hi
  have hb0 := L.hβ_nonneg i hi
  have hik : (i : ℝ) ≤ k := by exact_mod_cast hi
  have hbk : L.β i ≤ (4 * (k : ℝ)) * ‖L.H‖ := hb.trans (by nlinarith)
  rcases Nat.lt_or_ge i k with hlt | hge
  · rw [vnorm_smul, abs_of_nonneg hb0]
    have hv := L.vnorm_v_le_two (show 1 ≤ i + 1 by omega) (show i + 1 ≤ k by omega)
    calc
      L.β i * vnorm (L.v (i + 1)) ≤ ((4 * (k : ℝ)) * ‖L.H‖) * 2 :=
        mul_le_mul hbk hv (vnorm_nonneg _) (by positivity)
      _ = (8 * (k : ℝ)) * ‖L.H‖ := by ring
  · have hik' : i = k := le_antisymm hi hge
    subst hik'
    have hraw := L.rawBoundary_vnorm_le
    have hsqrt : Real.sqrt (1 + L.ε) ≤ 2 := by
      rw [Real.sqrt_le_iff]
      constructor
      · norm_num
      · nlinarith [L.epsilon_le_one]
    calc
      vnorm (L.β i • L.v (i + 1)) ≤ Real.sqrt (1 + L.ε) * L.β i := hraw
      _ ≤ 2 * ((4 * (i : ℝ)) * ‖L.H‖) :=
        mul_le_mul hsqrt hbk hb0 (by norm_num)
      _ = (8 * (i : ℝ)) * ‖L.H‖ := by ring

theorem normalizedF_bound {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ k) :
    vnorm (L.normalizedF j) ≤ (1500 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  have hs : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
  have hjk : (j : ℝ) ≤ k := by exact_mod_cast hj
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hid := L.normalizedF_sub_identity hj
  have hsplit : L.normalizedF j =
      (L.normScale j)⁻¹ • L.f j +
        (((L.normScale j)⁻¹ - (L.normScale (j - 1))⁻¹) •
            (L.β (j - 1) • L.v (j - 1)) +
          ((L.normScale j)⁻¹ - (L.normScale (j + 1))⁻¹) •
            (L.β j • L.v (j + 1))) := by
    rw [← hid]
    abel
  have hf : vnorm ((L.normScale j)⁻¹ • L.f j) ≤ (1400 * (k : ℝ)) * L.ε * ‖L.H‖ := by
    rw [vnorm_smul, abs_of_nonneg (inv_nonneg.mpr (L.normScale_nonneg j))]
    have hd := L.normScale_inv_le_two hj1 (by omega)
    have hfj := L.recurrence_error_bound j hj1 hj
    calc
      (L.normScale j)⁻¹ * vnorm (L.f j) ≤
          2 * ((700 * (j : ℝ)) * L.ε * ‖L.H‖) :=
        mul_le_mul hd hfj (vnorm_nonneg _) (by norm_num)
      _ ≤ (1400 * (k : ℝ)) * L.ε * ‖L.H‖ := by nlinarith
  have hprev : vnorm (((L.normScale j)⁻¹ - (L.normScale (j - 1))⁻¹) •
      (L.β (j - 1) • L.v (j - 1))) ≤ (32 * (k : ℝ)) * L.ε * ‖L.H‖ := by
    by_cases hj0 : j - 1 = 0
    · rw [hj0, L.hβ_zero, zero_smul, smul_zero, vnorm_zero]
      have := L.hε_nonneg
      positivity
    · rw [vnorm_smul]
      have hd := L.normScale_inv_sub hj1 (show j ≤ k + 1 by omega)
        (show 1 ≤ j - 1 by omega) (show j - 1 ≤ k + 1 by omega)
      have hv := L.vnorm_beta_smul_v_le (show j - 1 ≤ k by omega)
      calc
        |(L.normScale j)⁻¹ - (L.normScale (j - 1))⁻¹| *
            vnorm (L.β (j - 1) • L.v (j - 1)) ≤
            (4 * L.ε) * ((8 * (k : ℝ)) * ‖L.H‖) :=
          mul_le_mul hd hv (vnorm_nonneg _) (by have := L.hε_nonneg; positivity)
        _ = (32 * (k : ℝ)) * L.ε * ‖L.H‖ := by ring
  have hnext : vnorm (((L.normScale j)⁻¹ - (L.normScale (j + 1))⁻¹) •
      (L.β j • L.v (j + 1))) ≤ (32 * (k : ℝ)) * L.ε * ‖L.H‖ := by
    rw [vnorm_smul]
    have hd := L.normScale_inv_sub hj1 (show j ≤ k + 1 by omega)
      (show 1 ≤ j + 1 by omega) (show j + 1 ≤ k + 1 by omega)
    have hv := L.vnorm_beta_smul_v_succ_le hj
    calc
      |(L.normScale j)⁻¹ - (L.normScale (j + 1))⁻¹| *
          vnorm (L.β j • L.v (j + 1)) ≤
          (4 * L.ε) * ((8 * (k : ℝ)) * ‖L.H‖) :=
        mul_le_mul hd hv (vnorm_nonneg _) (by have := L.hε_nonneg; positivity)
      _ = (32 * (k : ℝ)) * L.ε * ‖L.H‖ := by ring
  rw [hsplit]
  calc
    _ ≤ vnorm ((L.normScale j)⁻¹ • L.f j) +
          (vnorm (((L.normScale j)⁻¹ - (L.normScale (j - 1))⁻¹) •
              (L.β (j - 1) • L.v (j - 1))) +
            vnorm (((L.normScale j)⁻¹ - (L.normScale (j + 1))⁻¹) •
              (L.β j • L.v (j + 1)))) :=
      (vnorm_add_le _ _).trans (add_le_add le_rfl (vnorm_add_le _ _))
    _ ≤ (1400 * (k : ℝ)) * L.ε * ‖L.H‖ +
          ((32 * (k : ℝ)) * L.ε * ‖L.H‖ + (32 * (k : ℝ)) * L.ε * ‖L.H‖) :=
      add_le_add hf (add_le_add hprev hnext)
    _ ≤ (1500 * (k : ℝ)) * L.ε * ‖L.H‖ := by nlinarith

theorem normalizedP_bound {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ k) :
    |L.normalizedP j| ≤ (4800 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  rw [L.normalizedP_identity hj, abs_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (L.normScale_nonneg j)),
    abs_of_nonneg (inv_nonneg.mpr (L.normScale_nonneg (j + 1)))]
  have hd1 := L.normScale_inv_le_two hj1 (by omega)
  have hd2 := L.normScale_inv_le_two (show 1 ≤ j + 1 by omega) (by omega)
  have hp := L.local_product_bound j hj1 hj
  have hjk : (j : ℝ) ≤ k := by exact_mod_cast hj
  have hs : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
  calc
    (L.normScale j)⁻¹ * (L.normScale (j + 1))⁻¹ * |L.p j| ≤
        2 * 2 * ((1200 * (j : ℝ)) * L.ε * ‖L.H‖) := by
      gcongr
      all_goals exact inv_nonneg.mpr (L.normScale_nonneg _)
    _ ≤ (4800 * (k : ℝ)) * L.ε * ‖L.H‖ := by nlinarith

structure NormalizedLocalErrors : Prop where
  residual : ∀ j, 1 ≤ j → j ≤ k →
    vnorm (L.normalizedF j) ≤ (1500 * (k : ℝ)) * L.ε * ‖L.H‖
  product : ∀ j, 1 ≤ j → j ≤ k →
    |L.normalizedP j| ≤ (4800 * (k : ℝ)) * L.ε * ‖L.H‖

theorem normalized_local_errors : L.NormalizedLocalErrors where
  residual _ hj1 hj := L.normalizedF_bound hj1 hj
  product _ hj1 hj := L.normalizedP_bound hj1 hj

/-- Columnwise square-root estimate used in the paper's commutator proof. -/
theorem normalizedFmat_bound_sqrt :
    ‖L.normalizedFmat‖ ≤ Real.sqrt (k : ℝ) * ((1500 * (k : ℝ)) * L.ε * ‖L.H‖) := by
  apply norm_ofCols_le_sqrt_card
  · exact mul_nonneg (mul_nonneg (by positivity) L.hε_nonneg) (norm_nonneg _)
  · intro j
    have h := L.normalizedF_bound (j := j.1 + 1) (by omega) (by omega)
    exact h

theorem normalizedFmat_bound :
    ‖L.normalizedFmat‖ ≤ (1500 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖ := by
  have he := L.hε_nonneg
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have hs : Real.sqrt (k : ℝ) ≤ k := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg k), Real.sqrt_nonneg (k : ℝ)]
  calc
    _ ≤ Real.sqrt (k : ℝ) * ((1500 * (k : ℝ)) * L.ε * ‖L.H‖) := L.normalizedFmat_bound_sqrt
    _ ≤ (k : ℝ) * ((1500 * (k : ℝ)) * L.ε * ‖L.H‖) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by ring

end LanczosRun
end FinitePrecisionLanczos
