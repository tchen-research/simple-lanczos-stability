import FinitePrecisionLanczos.Lanczos.Run


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

/-- Both elementary inequalities printed in coefficient Step 3, on the full stated interval. -/
lemma coefficient_multipliers {e : ℝ} (he : 0 ≤ e) (he20 : e ≤ 1 / 20) :
    (1 + 2 * e) * (1 + 5 * e) * (1 + e) * Real.sqrt (1 + e) ≤ 1 + 10 * e ∧
    (1 + 2 * e) * (1 + 5 * e) * (1 + e) ^ 2 * Real.sqrt (1 + e) ≤ 2 := by
  have hs : Real.sqrt (1 + e) ≤ 1 + e / 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + e by linarith), Real.sqrt_nonneg (1 + e), sq_nonneg e]
  have h2 : e ^ 2 ≤ e / 20 := by nlinarith
  have h3 : e ^ 3 ≤ e ^ 2 / 20 := by
    nlinarith [mul_nonneg (sq_nonneg e) (show 0 ≤ 1 / 20 - e by linarith)]
  have h4 : e ^ 4 ≤ e ^ 3 / 20 := by
    nlinarith [mul_nonneg (pow_nonneg he 3) (show 0 ≤ 1 / 20 - e by linarith)]
  have hm : (1 + 2 * e) * (1 + 5 * e) * (1 + e) * Real.sqrt (1 + e) ≤ 1 + 10 * e := by
    calc
      _ ≤ (1 + 2 * e) * (1 + 5 * e) * (1 + e) * (1 + e / 2) := by gcongr
      _ ≤ 1 + 10 * e := by nlinarith
  refine ⟨hm, ?_⟩
  calc
    _ = ((1 + 2 * e) * (1 + 5 * e) * (1 + e) * Real.sqrt (1 + e)) * (1 + e) := by ring
    _ ≤ (1 + 10 * e) * (1 + e) := by gcongr
    _ ≤ 2 := by nlinarith

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

lemma epsilon_le_one_hundredth : L.ε ≤ 1 / 100 := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  nlinarith [L.hsmall, L.hε_nonneg]

lemma epsilon_le_one : L.ε ≤ 1 :=
  (L.epsilon_le_one_hundredth).trans (by norm_num)

lemma near_unit_sq {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    1 - L.ε ≤ vnorm (L.v j) ^ 2 ∧ vnorm (L.v j) ^ 2 ≤ 1 + L.ε := by
  have h := abs_le.mp (L.hnear j hj1 hjk)
  constructor <;> linarith

lemma vnorm_v_le_one_add_epsilon {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    vnorm (L.v j) ≤ 1 + L.ε := by
  have hs := (L.near_unit_sq hj1 hjk).2
  have hv := vnorm_nonneg (L.v j)
  have he := L.hε_nonneg
  nlinarith [sq_nonneg (vnorm (L.v j) + (1 + L.ε))]

lemma vnorm_v_le_two {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    vnorm (L.v j) ≤ 2 := by
  have := L.vnorm_v_le_one_add_epsilon hj1 hjk
  have := L.epsilon_le_one
  linarith

private lemma scale_factor_times_next_norm {j : ℕ} (hj : j < k)
    (hb : L.β (j + 1) ≠ 0) :
    1 + L.ε ≤ (1 + 2 * L.ε) * vnorm (L.v (j + 2)) := by
  have hs : 1 - L.ε ≤ vnorm (L.v (j + 2)) ^ 2 := by
    by_cases hlast : j + 1 = k
    · have h := abs_le.mp (L.hnext (by simpa [hlast] using hb))
      have hj2 : j + 2 = k + 1 := by omega
      rw [hj2]
      linarith
    · have hj2_le : j + 2 ≤ k := Nat.succ_le_iff.mpr
          (lt_of_le_of_ne (Nat.succ_le_iff.mpr hj) hlast)
      exact (L.near_unit_sq (by omega) hj2_le).1
  have hv := vnorm_nonneg (L.v (j + 2))
  have he0 := L.hε_nonneg
  have he1 := L.epsilon_le_one_hundredth
  have hpoly : (1 + L.ε) ^ 2 ≤ (1 + 2 * L.ε) ^ 2 * (1 - L.ε) := by
    have hfac : 0 ≤ 1 - L.ε - 4 * L.ε ^ 2 := by
      nlinarith [sq_nonneg L.ε]
    nlinarith [mul_nonneg L.hε_nonneg hfac]
  have hsq : (1 + L.ε) ^ 2 ≤
      ((1 + 2 * L.ε) * vnorm (L.v (j + 2))) ^ 2 := by
    calc
      (1 + L.ε) ^ 2 ≤ (1 + 2 * L.ε) ^ 2 * (1 - L.ε) := hpoly
      _ ≤ (1 + 2 * L.ε) ^ 2 * vnorm (L.v (j + 2)) ^ 2 := by
        gcongr
      _ = ((1 + 2 * L.ε) * vnorm (L.v (j + 2))) ^ 2 := by ring
  have hleft : 0 ≤ 1 + L.ε := by linarith
  have hright : 0 ≤ (1 + 2 * L.ε) * vnorm (L.v (j + 2)) :=
    mul_nonneg (by linarith) hv
  nlinarith [sq_nonneg
    ((1 + 2 * L.ε) * vnorm (L.v (j + 2)) + (1 + L.ε))]

theorem normalization_scale_upper (j : ℕ) (hj : j < k) :
    L.β (j + 1) ≤ (1 + 2 * L.ε) * vnorm (L.z (j + 1)) := by
  by_cases hb : L.β (j + 1) = 0
  · rw [hb]
    exact mul_nonneg (by linarith [L.hε_nonneg]) (vnorm_nonneg _)
  · have hβ0 : 0 ≤ L.β (j + 1) := L.hβ_nonneg _ (Nat.succ_le_iff.mpr hj)
    have heq := congrArg vnorm (L.h_be j hj)
    rw [vnorm_smul, abs_of_nonneg hβ0] at heq
    have htri : vnorm (L.z (j + 1) + L.Δ (j + 1))
        ≤ (1 + L.ε) * vnorm (L.z (j + 1)) := by
      calc
        vnorm (L.z (j + 1) + L.Δ (j + 1))
            ≤ vnorm (L.z (j + 1)) + vnorm (L.Δ (j + 1)) := vnorm_add_le _ _
        _ ≤ vnorm (L.z (j + 1)) + L.ε * vnorm (L.z (j + 1)) := by
          gcongr
          exact L.hΔ j hj
        _ = (1 + L.ε) * vnorm (L.z (j + 1)) := by ring
    have hprod : L.β (j + 1) * vnorm (L.v (j + 2))
        ≤ (1 + L.ε) * vnorm (L.z (j + 1)) := by
      rw [heq]
      exact htri
    have hfactor := L.scale_factor_times_next_norm hj hb
    by_contra hnot
    have hstrict : (1 + 2 * L.ε) * vnorm (L.z (j + 1)) < L.β (j + 1) :=
      lt_of_not_ge hnot
    have hv := vnorm_nonneg (L.v (j + 2))
    have hz := vnorm_nonneg (L.z (j + 1))
    have hpositive : 0 < vnorm (L.v (j + 2)) := by
      by_contra hv0
      have : vnorm (L.v (j + 2)) = 0 := le_antisymm (le_of_not_gt hv0) hv
      rw [this, mul_zero] at hfactor
      linarith [L.hε_nonneg]
    have hmul := mul_lt_mul_of_pos_right hstrict hpositive
    nlinarith

lemma projection_sq_identity (j : ℕ) (hj : j < k) :
    vnorm (L.w (j + 1) - vdot (L.v (j + 1)) (L.w (j + 1)) • L.v (j + 1)) ^ 2
      = vnorm (L.w (j + 1)) ^ 2
        - (2 - vnorm (L.v (j + 1)) ^ 2)
          * vdot (L.v (j + 1)) (L.w (j + 1)) ^ 2 := by
  rw [vnorm_sq, vnorm_sq, vnorm_sq]
  simp only [vdot, sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  rw [dotProduct_comm (L.w (j + 1)) (L.v (j + 1))]
  ring

lemma projection_contract (j : ℕ) (hj : j < k) :
    vnorm (L.w (j + 1) - vdot (L.v (j + 1)) (L.w (j + 1)) • L.v (j + 1))
      ≤ vnorm (L.w (j + 1)) := by
  have hj1 : 1 ≤ j + 1 := by omega
  have hjk : j + 1 ≤ k := Nat.succ_le_iff.mpr hj
  have hv2 := (L.near_unit_sq hj1 hjk).2
  have hcoeff : 0 ≤ 2 - vnorm (L.v (j + 1)) ^ 2 := by
    have he := L.epsilon_le_one
    linarith
  have hsquares := L.projection_sq_identity j hj
  have hsq :
      vnorm (L.w (j + 1) - vdot (L.v (j + 1)) (L.w (j + 1)) • L.v (j + 1)) ^ 2
        ≤ vnorm (L.w (j + 1)) ^ 2 := by
    rw [hsquares]
    exact sub_le_self _ (mul_nonneg hcoeff (sq_nonneg _))
  nlinarith [vnorm_nonneg
    (L.w (j + 1) - vdot (L.v (j + 1)) (L.w (j + 1)) • L.v (j + 1)),
    vnorm_nonneg (L.w (j + 1))]

lemma alpha_bound (j : ℕ) (hj : j < k) :
    |L.α (j + 1)| ≤
      (1 + L.ε) * vnorm (L.v (j + 1)) * vnorm (L.w (j + 1)) := by
  have hdot := abs_vdot_le (L.v (j + 1)) (L.w (j + 1))
  have herr := L.heal j hj
  rw [L.h_al j hj]
  calc
    |vdot (L.v (j + 1)) (L.w (j + 1)) + L.eα (j + 1)|
        ≤ |vdot (L.v (j + 1)) (L.w (j + 1))| + |L.eα (j + 1)| :=
          abs_add_le _ _
    _ ≤ vnorm (L.v (j + 1)) * vnorm (L.w (j + 1))
        + L.ε * vnorm (L.v (j + 1)) * vnorm (L.w (j + 1)) :=
          add_le_add hdot herr
    _ = (1 + L.ε) * vnorm (L.v (j + 1)) * vnorm (L.w (j + 1)) := by ring

lemma z_relative_bound (j : ℕ) (hj : j < k) :
    vnorm (L.z (j + 1)) ≤ (1 + 5 * L.ε) * vnorm (L.w (j + 1)) := by
  let q := vdot (L.v (j + 1)) (L.w (j + 1))
  have hzdecomp :
      L.z (j + 1) =
        (L.w (j + 1) - q • L.v (j + 1))
          - L.eα (j + 1) • L.v (j + 1) + L.ez (j + 1) := by
    rw [L.h_z j hj, L.h_al j hj]
    dsimp [q]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hj1 : 1 ≤ j + 1 := by omega
  have hjk : j + 1 ≤ k := Nat.succ_le_iff.mpr hj
  have hv2 := (L.near_unit_sq hj1 hjk).2
  have hproj := L.projection_contract j hj
  have healv : |L.eα (j + 1)| * vnorm (L.v (j + 1))
      ≤ L.ε * (1 + L.ε) * vnorm (L.w (j + 1)) := by
    calc
      |L.eα (j + 1)| * vnorm (L.v (j + 1))
          ≤ (L.ε * vnorm (L.v (j + 1)) * vnorm (L.w (j + 1)))
              * vnorm (L.v (j + 1)) := by
            exact mul_le_mul_of_nonneg_right (L.heal j hj) (vnorm_nonneg _)
      _ = L.ε * vnorm (L.v (j + 1)) ^ 2 * vnorm (L.w (j + 1)) := by ring
      _ ≤ L.ε * (1 + L.ε) * vnorm (L.w (j + 1)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hv2 L.hε_nonneg) (vnorm_nonneg _)
  have hez : vnorm (L.ez (j + 1))
      ≤ L.ε * (1 + (1 + L.ε) ^ 2) * vnorm (L.w (j + 1)) := by
    calc
      vnorm (L.ez (j + 1))
          ≤ L.ε * (vnorm (L.w (j + 1))
              + |L.α (j + 1)| * vnorm (L.v (j + 1))) := L.hez j hj
      _ ≤ L.ε * (vnorm (L.w (j + 1))
              + ((1 + L.ε) * vnorm (L.v (j + 1))
                    * vnorm (L.w (j + 1))) * vnorm (L.v (j + 1))) := by
            apply mul_le_mul_of_nonneg_left _ L.hε_nonneg
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_right (L.alpha_bound j hj)
                (vnorm_nonneg (L.v (j + 1))))
      _ = L.ε * (vnorm (L.w (j + 1))
              + (1 + L.ε) * vnorm (L.v (j + 1)) ^ 2
                    * vnorm (L.w (j + 1))) := by ring
      _ ≤ L.ε * (vnorm (L.w (j + 1))
              + (1 + L.ε) * (1 + L.ε) * vnorm (L.w (j + 1))) := by
            apply mul_le_mul_of_nonneg_left _ L.hε_nonneg
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hv2 (by linarith [L.hε_nonneg]))
              (vnorm_nonneg (L.w (j + 1))))
      _ = L.ε * (1 + (1 + L.ε) ^ 2) * vnorm (L.w (j + 1)) := by ring
  have hraw : vnorm (L.z (j + 1))
      ≤ (1 + L.ε * (1 + L.ε) + L.ε * (1 + (1 + L.ε) ^ 2))
          * vnorm (L.w (j + 1)) := by
    rw [hzdecomp]
    calc
      vnorm ((L.w (j + 1) - q • L.v (j + 1))
          - L.eα (j + 1) • L.v (j + 1) + L.ez (j + 1))
          ≤ vnorm ((L.w (j + 1) - q • L.v (j + 1))
              - L.eα (j + 1) • L.v (j + 1)) + vnorm (L.ez (j + 1)) :=
            vnorm_add_le _ _
      _ ≤ vnorm (L.w (j + 1) - q • L.v (j + 1))
              + vnorm (L.eα (j + 1) • L.v (j + 1))
              + vnorm (L.ez (j + 1)) := by
            gcongr
            exact vnorm_sub_le _ _
      _ = vnorm (L.w (j + 1) - q • L.v (j + 1))
              + |L.eα (j + 1)| * vnorm (L.v (j + 1))
              + vnorm (L.ez (j + 1)) := by rw [vnorm_smul]
      _ ≤ vnorm (L.w (j + 1))
              + (L.ε * (1 + L.ε) * vnorm (L.w (j + 1)))
              + (L.ε * (1 + (1 + L.ε) ^ 2) * vnorm (L.w (j + 1))) := by
            gcongr
      _ = (1 + L.ε * (1 + L.ε) + L.ε * (1 + (1 + L.ε) ^ 2))
              * vnorm (L.w (j + 1)) := by ring
  have he0 := L.hε_nonneg
  have he1 := L.epsilon_le_one
  have he100 := L.epsilon_le_one_hundredth
  have hcubic : 0 ≤ L.ε ^ 2 * (1 - L.ε) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr he1)
  have he2 : L.ε ^ 2 ≤ L.ε / 100 := by
    nlinarith [mul_nonneg L.hε_nonneg (sub_nonneg.mpr he100)]
  have hcoef :
      1 + L.ε * (1 + L.ε) + L.ε * (1 + (1 + L.ε) ^ 2)
        ≤ 1 + 5 * L.ε := by
    nlinarith [sq_nonneg L.ε, hcubic]
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoef (vnorm_nonneg _))

lemma u_bound (j : ℕ) (hj : j < k) :
    vnorm (L.u (j + 1)) ≤ 2 * ‖L.H‖ := by
  have hj1 : 1 ≤ j + 1 := by omega
  have hjk : j + 1 ≤ k := Nat.succ_le_iff.mpr hj
  have hv := L.vnorm_v_le_one_add_epsilon hj1 hjk
  have hH := norm_nonneg L.H
  have hraw : vnorm (L.u (j + 1))
      ≤ (1 + L.ε) * ‖L.H‖ * vnorm (L.v (j + 1)) := by
    rw [L.h_u j hj]
    calc
      vnorm (L.H *ᵥ L.v (j + 1) + L.eu (j + 1))
          ≤ vnorm (L.H *ᵥ L.v (j + 1)) + vnorm (L.eu (j + 1)) :=
            vnorm_add_le _ _
      _ ≤ ‖L.H‖ * vnorm (L.v (j + 1))
            + L.ε * ‖L.H‖ * vnorm (L.v (j + 1)) :=
          add_le_add (vnorm_mulVec_le _ _) (L.heu j hj)
      _ = (1 + L.ε) * ‖L.H‖ * vnorm (L.v (j + 1)) := by ring
  calc
    vnorm (L.u (j + 1))
        ≤ (1 + L.ε) * ‖L.H‖ * vnorm (L.v (j + 1)) := hraw
    _ ≤ (1 + L.ε) * ‖L.H‖ * (1 + L.ε) := by
      exact mul_le_mul_of_nonneg_left hv
        (mul_nonneg (by linarith [L.hε_nonneg]) hH)
    _ ≤ 2 * ‖L.H‖ := by
      have he := L.epsilon_le_one_hundredth
      have he2 : L.ε ^ 2 ≤ L.ε / 100 := by
        nlinarith [mul_nonneg L.hε_nonneg (sub_nonneg.mpr he)]
      have hcoef : (1 + L.ε) ^ 2 ≤ 2 := by nlinarith
      calc
        (1 + L.ε) * ‖L.H‖ * (1 + L.ε) = (1 + L.ε) ^ 2 * ‖L.H‖ := by ring
        _ ≤ 2 * ‖L.H‖ := mul_le_mul_of_nonneg_right hcoef hH

lemma w_bound_from_beta (j : ℕ) (hj : j < k) :
    vnorm (L.w (j + 1))
      ≤ (1 + L.ε) * (2 * ‖L.H‖ + (1 + L.ε) * L.β j) := by
  have hβ0 : 0 ≤ L.β j := L.hβ_nonneg j (Nat.le_of_lt hj)
  have hvprev : vnorm (L.v j) ≤ 1 + L.ε := by
    by_cases hj0 : j = 0
    · subst j
      rw [L.hv_zero, vnorm_zero]
      linarith [L.hε_nonneg]
    · exact L.vnorm_v_le_one_add_epsilon (Nat.one_le_iff_ne_zero.mpr hj0)
        (Nat.le_of_lt hj)
  rw [L.h_w j hj]
  have hbase : vnorm (L.u (j + 1) - L.β j • L.v j)
      ≤ vnorm (L.u (j + 1)) + L.β j * vnorm (L.v j) := by
    calc
      vnorm (L.u (j + 1) - L.β j • L.v j)
          ≤ vnorm (L.u (j + 1)) + vnorm (L.β j • L.v j) := vnorm_sub_le _ _
      _ = vnorm (L.u (j + 1)) + L.β j * vnorm (L.v j) := by
        rw [vnorm_smul, abs_of_nonneg hβ0]
  calc
    vnorm (L.u (j + 1) - L.β j • L.v j + L.ew (j + 1))
        ≤ vnorm (L.u (j + 1) - L.β j • L.v j) + vnorm (L.ew (j + 1)) :=
          vnorm_add_le _ _
    _ ≤ (vnorm (L.u (j + 1)) + L.β j * vnorm (L.v j))
          + L.ε * (vnorm (L.u (j + 1)) + |L.β j| * vnorm (L.v j)) := by
        exact add_le_add hbase (L.hew j hj)
    _ = (1 + L.ε) * (vnorm (L.u (j + 1)) + L.β j * vnorm (L.v j)) := by
        rw [abs_of_nonneg hβ0]
        ring
    _ ≤ (1 + L.ε) * (2 * ‖L.H‖ + (1 + L.ε) * L.β j) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith [L.hε_nonneg])
        have hp := mul_le_mul_of_nonneg_left hvprev hβ0
        have hp' : L.β j * vnorm (L.v j) ≤ (1 + L.ε) * L.β j := by
          calc
            L.β j * vnorm (L.v j) ≤ L.β j * (1 + L.ε) := hp
            _ = (1 + L.ε) * L.β j := by ring
        exact add_le_add (L.u_bound j hj) hp'

/-- Near-unit columns, in the square-root form used in Step 2 of the paper. -/
lemma vnorm_v_le_sqrt {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    vnorm (L.v j) ≤ Real.sqrt (1 + L.ε) := by
  have hs := (L.near_unit_sq hj1 hjk).2
  have he : 0 ≤ 1 + L.ε := by linarith [L.hε_nonneg]
  nlinarith [Real.sq_sqrt he, Real.sqrt_nonneg (1 + L.ε), vnorm_nonneg (L.v j)]

lemma sqrt_one_add_epsilon_le : Real.sqrt (1 + L.ε) ≤ 1 + L.ε / 2 := by
  have he := L.hε_nonneg
  have hs := Real.sq_sqrt (show 0 ≤ 1 + L.ε by linarith)
  nlinarith [Real.sqrt_nonneg (1 + L.ε), sq_nonneg L.ε]

/-- Step 2: (1 + ε)^(3/2) ‖A‖, with the half power expressed as a square root. -/
lemma u_bound_sqrt (j : ℕ) (hj : j < k) :
    vnorm (L.u (j + 1)) ≤ (1 + L.ε) * Real.sqrt (1 + L.ε) * ‖L.H‖ := by
  have he := L.hε_nonneg
  calc
    vnorm (L.u (j + 1)) ≤ ‖L.H‖ * vnorm (L.v (j + 1)) +
        L.ε * ‖L.H‖ * vnorm (L.v (j + 1)) := by
      rw [L.h_u j hj]
      exact (vnorm_add_le _ _).trans (add_le_add (vnorm_mulVec_le _ _) (L.heu j hj))
    _ = (1 + L.ε) * vnorm (L.v (j + 1)) * ‖L.H‖ := by ring
    _ ≤ (1 + L.ε) * Real.sqrt (1 + L.ε) * ‖L.H‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (L.vnorm_v_le_sqrt (j := j + 1) (by omega) (by omega))
          (by linarith)) (norm_nonneg _)

/-- Step 2: the two terms with exponents 5/2 and 3/2, respectively. -/
lemma w_bound_from_beta_sqrt (j : ℕ) (hj : j < k) :
    vnorm (L.w (j + 1)) ≤
      (1 + L.ε) ^ 2 * Real.sqrt (1 + L.ε) * ‖L.H‖ +
        (1 + L.ε) * Real.sqrt (1 + L.ε) * L.β j := by
  have he := L.hε_nonneg
  have hβ := L.hβ_nonneg j (by omega)
  have hv : vnorm (L.v j) ≤ Real.sqrt (1 + L.ε) := by
    by_cases h : j = 0
    · simp [h, L.hv_zero, Real.sqrt_nonneg]
    · exact L.vnorm_v_le_sqrt (by omega) (by omega)
  calc
    vnorm (L.w (j + 1)) ≤ (1 + L.ε) *
        (vnorm (L.u (j + 1)) + L.β j * vnorm (L.v j)) := by
      rw [L.h_w j hj]
      have h := (vnorm_add_le (L.u (j + 1) - L.β j • L.v j) (L.ew (j + 1))).trans
        (add_le_add ((vnorm_sub_le _ _).trans
          (by rw [vnorm_smul, abs_of_nonneg hβ])) (L.hew j hj))
      rw [abs_of_nonneg hβ] at h
      nlinarith
    _ ≤ (1 + L.ε) * ((1 + L.ε) * Real.sqrt (1 + L.ε) * ‖L.H‖ +
        L.β j * Real.sqrt (1 + L.ε)) := by
      gcongr
      exact L.u_bound_sqrt j hj
    _ = _ := by ring

/-- The elementary multiplier inequality in Step 3. -/
lemma beta_multiplier_bound :
    (1 + 2 * L.ε) * (1 + 5 * L.ε) * (1 + L.ε) * Real.sqrt (1 + L.ε) ≤
      1 + 10 * L.ε := by
  exact (coefficient_multipliers L.hε_nonneg
    (L.epsilon_le_one_hundredth.trans (by norm_num))).1

/-- The paper's sharper scalar recurrence (Step 3). -/
theorem beta_recurrence_paper (j : ℕ) (hj : j < k) :
    L.β (j + 1) ≤ (1 + 10 * L.ε) * L.β j + 2 * ‖L.H‖ := by
  have he := L.hε_nonneg
  have he100 := L.epsilon_le_one_hundredth
  have hβ := L.hβ_nonneg j (by omega)
  have hc := L.beta_multiplier_bound
  have ha : (1 + 2 * L.ε) * (1 + 5 * L.ε) * (1 + L.ε) ^ 2 *
      Real.sqrt (1 + L.ε) ≤ 2 := by
    calc
      _ = ((1 + 2 * L.ε) * (1 + 5 * L.ε) * (1 + L.ε) * Real.sqrt (1 + L.ε)) *
          (1 + L.ε) := by ring
      _ ≤ (1 + 10 * L.ε) * (1 + L.ε) := by gcongr
      _ ≤ 2 := by nlinarith
  calc
    L.β (j + 1) ≤ (1 + 2 * L.ε) * ((1 + 5 * L.ε) * vnorm (L.w (j + 1))) :=
      (L.normalization_scale_upper j hj).trans
        (mul_le_mul_of_nonneg_left (L.z_relative_bound j hj) (by positivity))
    _ ≤ (1 + 2 * L.ε) * ((1 + 5 * L.ε) *
        ((1 + L.ε) ^ 2 * Real.sqrt (1 + L.ε) * ‖L.H‖ +
          (1 + L.ε) * Real.sqrt (1 + L.ε) * L.β j)) := by
      gcongr
      exact L.w_bound_from_beta_sqrt j hj
    _ = ((1 + 2 * L.ε) * (1 + 5 * L.ε) * (1 + L.ε) * Real.sqrt (1 + L.ε)) * L.β j +
        ((1 + 2 * L.ε) * (1 + 5 * L.ε) * (1 + L.ε) ^ 2 * Real.sqrt (1 + L.ε)) * ‖L.H‖ := by ring
    _ ≤ (1 + 10 * L.ε) * L.β j + 2 * ‖L.H‖ := by gcongr

lemma beta_recurrence (j : ℕ) (hj : j < k) :
    L.β (j + 1) ≤ 3 * ‖L.H‖ + (1 + 12 * L.ε) * L.β j := by
  have h := L.beta_recurrence_paper j hj
  have hβ := L.hβ_nonneg j (Nat.le_of_lt hj)
  nlinarith [mul_nonneg L.hε_nonneg hβ, norm_nonneg L.H]

theorem beta_bound (j : ℕ) (hjk : j ≤ k) :
    L.β j ≤ (4 * (j : ℝ)) * ‖L.H‖ := by
  induction j with
  | zero => simp [L.hβ_zero]
  | succ j ih =>
    have hj : j < k := by omega
    have he := L.hε_nonneg
    have hjε : (j : ℝ) * L.ε ≤ 1 / 100 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast (show j ≤ k by omega))
        L.hε_nonneg).trans L.hsmall
    have htail : (40 * (j : ℝ) * L.ε) * ‖L.H‖ ≤ 2 * ‖L.H‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    calc
      L.β (j + 1) ≤ (1 + 10 * L.ε) * L.β j + 2 * ‖L.H‖ := L.beta_recurrence_paper j hj
      _ ≤ (1 + 10 * L.ε) * ((4 * (j : ℝ)) * ‖L.H‖) + 2 * ‖L.H‖ := by
        gcongr
        exact ih (by omega)
      _ = (4 * (j : ℝ)) * ‖L.H‖ + (40 * (j : ℝ) * L.ε) * ‖L.H‖ + 2 * ‖L.H‖ := by ring
      _ ≤ (4 * ((j + 1 : ℕ) : ℝ)) * ‖L.H‖ := by push_cast; linarith

/-- The explicit constants printed in Step 4 of the coefficient proof. -/
structure PaperCoefficientBounds (j : ℕ) : Prop where
  u : vnorm (L.u j) ≤ 2 * ‖L.H‖
  w : vnorm (L.w j) ≤ (5 * (j : ℝ)) * ‖L.H‖
  alpha : |L.α j| ≤ (6 * (j : ℝ)) * ‖L.H‖
  z : vnorm (L.z j) ≤ (7 * (j : ℝ)) * ‖L.H‖
  beta : L.β j ≤ (4 * (j : ℝ)) * ‖L.H‖

theorem coefficients_paper (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    L.PaperCoefficientBounds j := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hj1)
  have hi : i < k := by omega
  have he := L.hε_nonneg
  have he100 := L.epsilon_le_one_hundredth
  have hH := norm_nonneg L.H
  have hwn := vnorm_nonneg (L.w (i + 1))
  have hvn := vnorm_nonneg (L.v (i + 1))
  have hβ := L.hβ_nonneg i (by omega)
  have hb := L.beta_bound i (by omega)
  have hw : vnorm (L.w (i + 1)) ≤ (5 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖ := by
    have hc : (1 + L.ε) ^ 2 ≤ 5 / 4 := by nlinarith
    calc
      _ ≤ (1 + L.ε) * (2 * ‖L.H‖ + (1 + L.ε) * L.β i) := L.w_bound_from_beta i hi
      _ = (2 * (1 + L.ε)) * ‖L.H‖ + (1 + L.ε) ^ 2 * L.β i := by ring
      _ ≤ 5 * ‖L.H‖ + (5 / 4) * ((4 * (i : ℝ)) * ‖L.H‖) := by gcongr <;> linarith
      _ = _ := by push_cast; ring
  have ha : |L.α (i + 1)| ≤ (6 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖ := by
    have hv := L.vnorm_v_le_one_add_epsilon (j := i + 1) (by omega) (by omega)
    have hc : (1 + L.ε) ^ 2 ≤ 6 / 5 := by nlinarith
    calc
      _ ≤ (1 + L.ε) * vnorm (L.v (i + 1)) * vnorm (L.w (i + 1)) := L.alpha_bound i hi
      _ ≤ (1 + L.ε) * (1 + L.ε) * ((5 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖) := by gcongr
      _ = (1 + L.ε) ^ 2 * ((5 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖) := by ring
      _ ≤ (6 / 5) * ((5 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖) := by gcongr
      _ = _ := by ring
  have hz : vnorm (L.z (i + 1)) ≤ (7 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖ := by
    calc
      _ ≤ (1 + 5 * L.ε) * vnorm (L.w (i + 1)) := L.z_relative_bound i hi
      _ ≤ (7 / 5) * ((5 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖) := by gcongr <;> linarith
      _ = _ := by ring
  exact ⟨L.u_bound i hi, hw, ha, hz, L.beta_bound _ hjk⟩

structure CoefficientEnvelope (j : ℕ) : Prop where
  u : vnorm (L.u j) ≤ (100 * (j : ℝ)) * ‖L.H‖
  w : vnorm (L.w j) ≤ (100 * (j : ℝ)) * ‖L.H‖
  alpha : |L.α j| ≤ (100 * (j : ℝ)) * ‖L.H‖
  z : vnorm (L.z j) ≤ (100 * (j : ℝ)) * ‖L.H‖
  beta : L.β j ≤ (100 * (j : ℝ)) * ‖L.H‖

/-- Compatibility envelope, now obtained from the paper's sharper constants. -/
theorem coefficients (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    L.CoefficientEnvelope j := by
  have h := L.coefficients_paper j hj1 hjk
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hH := norm_nonneg L.H
  constructor <;> nlinarith [h.u, h.w, h.alpha, h.z, h.beta]

lemma eu_explicit (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    vnorm (L.eu j) ≤ (2 * (j : ℝ)) * L.ε * ‖L.H‖ := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hj1)
  have hi : i < k := Nat.succ_le_iff.mp hjk
  have hv := L.vnorm_v_le_two (by omega) hjk
  calc
    vnorm (L.eu (i + 1))
        ≤ L.ε * ‖L.H‖ * vnorm (L.v (i + 1)) := L.heu i hi
    _ ≤ L.ε * ‖L.H‖ * 2 := by
      exact mul_le_mul_of_nonneg_left hv
        (mul_nonneg L.hε_nonneg (norm_nonneg _))
    _ ≤ (2 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by
      have hi1 : (1 : ℝ) ≤ (i + 1 : ℕ) := by exact_mod_cast Nat.succ_pos i
      have hs : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
      push_cast
      nlinarith

lemma ew_explicit (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    vnorm (L.ew j) ≤ (200 * (j : ℝ)) * L.ε * ‖L.H‖ := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hj1)
  have hi : i < k := Nat.succ_le_iff.mp hjk
  have hc := L.coefficients (i + 1) (by omega) hjk
  have hβ0 : 0 ≤ L.β i := L.hβ_nonneg i (Nat.le_of_lt hi)
  have hβ := L.beta_bound i (Nat.le_of_lt hi)
  have hvprev : vnorm (L.v i) ≤ 2 := by
    by_cases hi0 : i = 0
    · subst i
      simp [L.hv_zero]
    · exact L.vnorm_v_le_two (Nat.one_le_iff_ne_zero.mpr hi0) (Nat.le_of_lt hi)
  have hprod : |L.β i| * vnorm (L.v i) ≤ (8 * (i : ℝ)) * ‖L.H‖ := by
    rw [abs_of_nonneg hβ0]
    calc
      L.β i * vnorm (L.v i) ≤ ((4 * (i : ℝ)) * ‖L.H‖) * vnorm (L.v i) :=
        mul_le_mul_of_nonneg_right hβ (vnorm_nonneg _)
      _ ≤ ((4 * (i : ℝ)) * ‖L.H‖) * 2 := by
        exact mul_le_mul_of_nonneg_left hvprev
          (mul_nonneg (by positivity) (norm_nonneg _))
      _ = (8 * (i : ℝ)) * ‖L.H‖ := by ring
  have hinside : vnorm (L.u (i + 1)) + |L.β i| * vnorm (L.v i)
      ≤ (108 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖ := by
    calc
      vnorm (L.u (i + 1)) + |L.β i| * vnorm (L.v i)
          ≤ (100 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖
              + (8 * (i : ℝ)) * ‖L.H‖ := add_le_add hc.u hprod
      _ ≤ (108 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖ := by
        push_cast
        nlinarith [norm_nonneg L.H]
  calc
    vnorm (L.ew (i + 1))
        ≤ L.ε * (vnorm (L.u (i + 1)) + |L.β i| * vnorm (L.v i)) := L.hew i hi
    _ ≤ L.ε * ((108 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖) :=
      mul_le_mul_of_nonneg_left hinside L.hε_nonneg
    _ ≤ (200 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by
      have hs : 0 ≤ ((i + 1 : ℕ) : ℝ) * L.ε * ‖L.H‖ :=
        mul_nonneg (mul_nonneg (by positivity) L.hε_nonneg) (norm_nonneg _)
      nlinarith

lemma ealpha_explicit (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    |L.eα j| ≤ (200 * (j : ℝ)) * L.ε * ‖L.H‖ := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hj1)
  have hi : i < k := Nat.succ_le_iff.mp hjk
  have hc := L.coefficients (i + 1) (by omega) hjk
  have hv := L.vnorm_v_le_two (by omega) hjk
  calc
    |L.eα (i + 1)|
        ≤ L.ε * vnorm (L.v (i + 1)) * vnorm (L.w (i + 1)) := L.heal i hi
    _ ≤ L.ε * 2 * ((100 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hv L.hε_nonneg) hc.w
        (vnorm_nonneg _) (mul_nonneg L.hε_nonneg (by positivity))
    _ = (200 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by ring

lemma ez_explicit (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    vnorm (L.ez j) ≤ (300 * (j : ℝ)) * L.ε * ‖L.H‖ := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hj1)
  have hi : i < k := Nat.succ_le_iff.mp hjk
  have hc := L.coefficients (i + 1) (by omega) hjk
  have hv := L.vnorm_v_le_two (by omega) hjk
  have hinside : vnorm (L.w (i + 1)) + |L.α (i + 1)| * vnorm (L.v (i + 1))
      ≤ (300 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖ := by
    calc
      vnorm (L.w (i + 1)) + |L.α (i + 1)| * vnorm (L.v (i + 1))
          ≤ (100 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖
              + ((100 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖) * 2 := by
            exact add_le_add hc.w (mul_le_mul hc.alpha hv (vnorm_nonneg _) (by positivity))
      _ = (300 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖ := by ring
  calc
    vnorm (L.ez (i + 1))
        ≤ L.ε * (vnorm (L.w (i + 1)) + |L.α (i + 1)| * vnorm (L.v (i + 1))) :=
          L.hez i hi
    _ ≤ L.ε * ((300 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖) :=
          mul_le_mul_of_nonneg_left hinside L.hε_nonneg
    _ = (300 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by ring

lemma delta_explicit (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    vnorm (L.Δ j) ≤ (100 * (j : ℝ)) * L.ε * ‖L.H‖ := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hj1)
  have hi : i < k := Nat.succ_le_iff.mp hjk
  have hc := L.coefficients (i + 1) (by omega) hjk
  calc
    vnorm (L.Δ (i + 1)) ≤ L.ε * vnorm (L.z (i + 1)) := L.hΔ i hi
    _ ≤ L.ε * ((100 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖) :=
      mul_le_mul_of_nonneg_left hc.z L.hε_nonneg
    _ = (100 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by ring

theorem recurrence_error_bound (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    vnorm (L.f j) ≤ (700 * (j : ℝ)) * L.ε * ‖L.H‖ := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.one_le_iff_ne_zero.mp hj1)
  have hi : i < k := Nat.succ_le_iff.mp hjk
  have heu := L.eu_explicit (i + 1) hj1 hjk
  have hew := L.ew_explicit (i + 1) hj1 hjk
  have hez := L.ez_explicit (i + 1) hj1 hjk
  have hΔ := L.delta_explicit (i + 1) hj1 hjk
  rw [L.recurrence_error_identity i hi, vnorm_neg]
  calc
    vnorm (L.eu (i + 1) + L.ew (i + 1) + L.ez (i + 1) + L.Δ (i + 1))
        ≤ vnorm (L.eu (i + 1) + L.ew (i + 1) + L.ez (i + 1)) +
            vnorm (L.Δ (i + 1)) := vnorm_add_le _ _
    _ ≤ vnorm (L.eu (i + 1) + L.ew (i + 1)) + vnorm (L.ez (i + 1)) +
          vnorm (L.Δ (i + 1)) := by
      gcongr
      exact vnorm_add_le _ _
    _ ≤ vnorm (L.eu (i + 1)) + vnorm (L.ew (i + 1)) +
          vnorm (L.ez (i + 1)) + vnorm (L.Δ (i + 1)) := by
      gcongr
      exact vnorm_add_le _ _
    _ ≤ (2 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖
          + (200 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖
          + (300 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖
          + (100 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by gcongr
    _ ≤ (700 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by
      have hs : 0 ≤ ((i + 1 : ℕ) : ℝ) * L.ε * ‖L.H‖ :=
        mul_nonneg (mul_nonneg (by positivity) L.hε_nonneg) (norm_nonneg _)
      nlinarith

lemma abs_g_le (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) : |L.g j| ≤ L.ε := by
  rw [g, ← vnorm_sq]
  exact L.hnear j hj1 hjk

theorem local_product_bound (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    |L.p j| ≤ (1200 * (j : ℝ)) * L.ε * ‖L.H‖ := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hj1)
  have hi : i < k := Nat.succ_le_iff.mp hjk
  have hid := L.local_product_identity i hi
  have hea := L.ealpha_explicit (i + 1) (by omega) hjk
  have hg := L.abs_g_le (i + 1) (by omega) hjk
  have hc := L.coefficients (i + 1) (by omega) hjk
  have hez := L.ez_explicit (i + 1) (by omega) hjk
  have hΔ := L.delta_explicit (i + 1) (by omega) hjk
  have hv := L.vnorm_v_le_two (by omega) hjk
  have hga : |L.g (i + 1) * L.α (i + 1)|
      ≤ (100 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by
    rw [abs_mul]
    calc
      |L.g (i + 1)| * |L.α (i + 1)|
          ≤ L.ε * ((100 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖) :=
            mul_le_mul hg hc.alpha (abs_nonneg _) L.hε_nonneg
      _ = (100 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by ring
  have hdotz : |vdot (L.v (i + 1)) (L.ez (i + 1))|
      ≤ (600 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by
    calc
      |vdot (L.v (i + 1)) (L.ez (i + 1))|
          ≤ vnorm (L.v (i + 1)) * vnorm (L.ez (i + 1)) := abs_vdot_le _ _
      _ ≤ 2 * ((300 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖) :=
            mul_le_mul hv hez (vnorm_nonneg _) (by positivity)
      _ = (600 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by ring
  have hdotΔ : |vdot (L.v (i + 1)) (L.Δ (i + 1))|
      ≤ (200 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by
    calc
      |vdot (L.v (i + 1)) (L.Δ (i + 1))|
          ≤ vnorm (L.v (i + 1)) * vnorm (L.Δ (i + 1)) := abs_vdot_le _ _
      _ ≤ 2 * ((100 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖) :=
            mul_le_mul hv hΔ (vnorm_nonneg _) (by positivity)
      _ = (200 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by ring
  have hsub : |-L.eα (i + 1) - L.g (i + 1) * L.α (i + 1)|
      ≤ |-L.eα (i + 1)| + |L.g (i + 1) * L.α (i + 1)| := by
    calc
      |-L.eα (i + 1) - L.g (i + 1) * L.α (i + 1)|
          = |-L.eα (i + 1) + -(L.g (i + 1) * L.α (i + 1))| := by
            rw [sub_eq_add_neg]
      _ ≤ |-L.eα (i + 1)| + |-(L.g (i + 1) * L.α (i + 1))| := abs_add_le _ _
      _ = |-L.eα (i + 1)| + |L.g (i + 1) * L.α (i + 1)| := by
        simp only [abs_neg]
  rw [hid]
  calc
    |-L.eα (i + 1) - L.g (i + 1) * L.α (i + 1)
        + vdot (L.v (i + 1)) (L.ez (i + 1))
        + vdot (L.v (i + 1)) (L.Δ (i + 1))|
      ≤ |L.eα (i + 1)| + |L.g (i + 1) * L.α (i + 1)|
          + |vdot (L.v (i + 1)) (L.ez (i + 1))|
          + |vdot (L.v (i + 1)) (L.Δ (i + 1))| := by
        calc
          _ ≤ |-L.eα (i + 1) - L.g (i + 1) * L.α (i + 1)
              + vdot (L.v (i + 1)) (L.ez (i + 1))|
              + |vdot (L.v (i + 1)) (L.Δ (i + 1))| := abs_add_le _ _
          _ ≤ (|-L.eα (i + 1) - L.g (i + 1) * L.α (i + 1)|
              + |vdot (L.v (i + 1)) (L.ez (i + 1))|)
              + |vdot (L.v (i + 1)) (L.Δ (i + 1))| := by
                exact add_le_add (abs_add_le _ _) le_rfl
          _ ≤ ((|-L.eα (i + 1)| + |L.g (i + 1) * L.α (i + 1)|)
              + |vdot (L.v (i + 1)) (L.ez (i + 1))|)
              + |vdot (L.v (i + 1)) (L.Δ (i + 1))| := by
                exact add_le_add (add_le_add hsub le_rfl) le_rfl
          _ = |L.eα (i + 1)| + |L.g (i + 1) * L.α (i + 1)|
              + |vdot (L.v (i + 1)) (L.ez (i + 1))|
              + |vdot (L.v (i + 1)) (L.Δ (i + 1))| := by rw [abs_neg]
    _ ≤ (200 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖
          + (100 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖
          + (600 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖
          + (200 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by gcongr
    _ ≤ (1200 * ((i + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := by
      have hs : 0 ≤ ((i + 1 : ℕ) : ℝ) * L.ε * ‖L.H‖ :=
        mul_nonneg (mul_nonneg (by positivity) L.hε_nonneg) (norm_nonneg _)
      nlinarith

theorem local_errors (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    vnorm (L.f j) ≤ (700 * (j : ℝ)) * L.ε * ‖L.H‖ ∧
      |L.g j| ≤ L.ε ∧
      |L.p j| ≤ (1200 * (j : ℝ)) * L.ε * ‖L.H‖ := by
  exact ⟨L.recurrence_error_bound j hj1 hjk, L.abs_g_le j hj1 hjk,
    L.local_product_bound j hj1 hjk⟩

end LanczosRun
end FinitePrecisionLanczos
