import FinitePrecisionLanczos.Lanczos.Run

/-!
# Explicit local bounds

This file proves the inequality layer for `lem:coefficients` and
`thm:local-errors`.  Unlike the PDF, every polynomial factor is an explicit
numeral and power of `k`.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- The explicit representative of the paper's assumption `eps \lesssim_k 1`. -/
lemma epsilon_le_one_hundredth : L.ε ≤ 1 / 100 := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  nlinarith [L.hsmall, L.hε_nonneg]

lemma epsilon_le_one : L.ε ≤ 1 :=
  (L.epsilon_le_one_hundredth).trans (by norm_num)

lemma epsilon_lt_one : L.ε < 1 :=
  (L.epsilon_le_one_hundredth).trans_lt (by norm_num)

/-- Squared-norm form of `ass:normalization`. -/
lemma near_unit_sq {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    1 - L.ε ≤ vnorm (L.v j) ^ 2 ∧ vnorm (L.v j) ^ 2 ≤ 1 + L.ε := by
  have h := abs_le.mp (L.hnear j hj1 hjk)
  constructor <;> linarith

/-- Convenient consequence of `ass:normalization`, used throughout the PDF. -/
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

/-- The normalized next vector has enough length to prove the returned-scale
factor used in `lem:coefficients`. -/
private lemma scale_factor_times_next_norm {j : ℕ} (hj : j < k)
    (hb : L.β (j + 1) ≠ 0) :
    1 + L.ε ≤ (1 + 2 * L.ε) * vnorm (L.v (j + 2)) := by
  -- `hnext` is stated only for the final boundary.  At internal edges the
  -- same near-unit fact is supplied by `hnear`.
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

/-- Returned-scale bound used in `lem:coefficients`, with factor `1+2 eps`. -/
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

/-- Exact rank-one identity used in the proof of `lem:coefficients`. -/
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

/-- The exact-arithmetic projection in the coefficient proof is nonexpansive. -/
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

/-- Explicit form of the inner-product estimate used below. -/
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

/-- The residual estimate appearing verbatim in the coefficient proof. -/
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

/-- Direct consequence of `eq:local-u`. -/
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

/-- Bound for the updated vector before projection. -/
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

/-- Scalar recurrence used to prove `lem:coefficients`, now with explicit constants. -/
lemma beta_recurrence (j : ℕ) (hj : j < k) :
    L.β (j + 1) ≤ 3 * ‖L.H‖ + (1 + 12 * L.ε) * L.β j := by
  have hb := L.normalization_scale_upper j hj
  have hz := L.z_relative_bound j hj
  have hw := L.w_bound_from_beta j hj
  have hH := norm_nonneg L.H
  have hβ0 : 0 ≤ L.β j := L.hβ_nonneg j (Nat.le_of_lt hj)
  have he0 := L.hε_nonneg
  have he := L.epsilon_le_one_hundredth
  have hraw : L.β (j + 1)
      ≤ (1 + 2 * L.ε) * (1 + 5 * L.ε) * (1 + L.ε)
          * (2 * ‖L.H‖ + (1 + L.ε) * L.β j) := by
    calc
      L.β (j + 1) ≤ (1 + 2 * L.ε) * vnorm (L.z (j + 1)) := hb
      _ ≤ (1 + 2 * L.ε) * ((1 + 5 * L.ε) * vnorm (L.w (j + 1))) := by gcongr
      _ ≤ (1 + 2 * L.ε) * ((1 + 5 * L.ε)
          * ((1 + L.ε) * (2 * ‖L.H‖ + (1 + L.ε) * L.β j))) := by gcongr
      _ = (1 + 2 * L.ε) * (1 + 5 * L.ε) * (1 + L.ε)
          * (2 * ‖L.H‖ + (1 + L.ε) * L.β j) := by ring
  have hA : 2 * ((1 + 2 * L.ε) * (1 + 5 * L.ε) * (1 + L.ε)) ≤ 3 := by
    nlinarith [sq_nonneg L.ε,
      mul_nonneg (sq_nonneg L.ε) (sub_nonneg.mpr L.epsilon_le_one)]
  have hB : (1 + 2 * L.ε) * (1 + 5 * L.ε) * (1 + L.ε) ^ 2
      ≤ 1 + 12 * L.ε := by
    have h2 : L.ε ^ 2 ≤ L.ε / 100 := by
      nlinarith [mul_nonneg L.hε_nonneg (sub_nonneg.mpr he)]
    have h3 : L.ε ^ 3 ≤ L.ε ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg L.ε) (sub_nonneg.mpr L.epsilon_le_one)]
    have h4 : L.ε ^ 4 ≤ L.ε ^ 3 := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ L.ε ^ 3)
        (sub_nonneg.mpr L.epsilon_le_one)]
    nlinarith
  calc
    L.β (j + 1)
        ≤ (1 + 2 * L.ε) * (1 + 5 * L.ε) * (1 + L.ε)
          * (2 * ‖L.H‖ + (1 + L.ε) * L.β j) := hraw
    _ = (2 * ((1 + 2 * L.ε) * (1 + 5 * L.ε) * (1 + L.ε))) * ‖L.H‖
          + ((1 + 2 * L.ε) * (1 + 5 * L.ε) * (1 + L.ε) ^ 2) * L.β j := by ring
    _ ≤ 3 * ‖L.H‖ + (1 + 12 * L.ε) * L.β j := by gcongr

/-- Explicit polynomial version of the geometric iteration in
`lem:coefficients`: `β_j ≤ 4 j ‖H‖`. -/
theorem beta_bound (j : ℕ) (hjk : j ≤ k) :
    L.β j ≤ (4 * (j : ℝ)) * ‖L.H‖ := by
  induction j with
  | zero => simp [L.hβ_zero]
  | succ j ih =>
      have hjlt : j < k := Nat.lt_of_succ_le hjk
      have hjle : j ≤ k := Nat.le_of_succ_le hjk
      have hrec := L.beta_recurrence j hjlt
      have hih := ih hjle
      have hfac0 : 0 ≤ 1 + 12 * L.ε := by linarith [L.hε_nonneg]
      have hjcast : (j : ℝ) ≤ k := by exact_mod_cast hjle
      have hjε : (j : ℝ) * L.ε ≤ 1 / 100 := by
        calc
          (j : ℝ) * L.ε ≤ (k : ℝ) * L.ε :=
            mul_le_mul_of_nonneg_right hjcast L.hε_nonneg
          _ ≤ 1 / 100 := L.hsmall
      have h48 : 48 * L.ε * (j : ℝ) ≤ 1 := by nlinarith
      have hH := norm_nonneg L.H
      have htail : (48 * L.ε * (j : ℝ)) * ‖L.H‖ ≤ ‖L.H‖ :=
        by simpa using (mul_le_mul_of_nonneg_right h48 hH)
      calc
        L.β (j + 1) ≤ 3 * ‖L.H‖ + (1 + 12 * L.ε) * L.β j := hrec
        _ ≤ 3 * ‖L.H‖ + (1 + 12 * L.ε) * ((4 * (j : ℝ)) * ‖L.H‖) := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hih hfac0)
        _ = 3 * ‖L.H‖ + (4 * (j : ℝ)) * ‖L.H‖
              + (48 * L.ε * (j : ℝ)) * ‖L.H‖ := by ring
        _ ≤ 3 * ‖L.H‖ + (4 * (j : ℝ)) * ‖L.H‖ + ‖L.H‖ := by
          exact add_le_add le_rfl htail
        _ = (4 * ((j + 1 : ℕ) : ℝ)) * ‖L.H‖ := by
          push_cast
          ring

/-- Fieldwise, human-auditable explicit form of `lem:coefficients`. -/
structure CoefficientEnvelope (j : ℕ) : Prop where
  u : vnorm (L.u j) ≤ (100 * (j : ℝ)) * ‖L.H‖
  w : vnorm (L.w j) ≤ (100 * (j : ℝ)) * ‖L.H‖
  alpha : |L.α j| ≤ (100 * (j : ℝ)) * ‖L.H‖
  z : vnorm (L.z j) ≤ (100 * (j : ℝ)) * ‖L.H‖
  beta : L.β j ≤ (100 * (j : ℝ)) * ‖L.H‖

/-- `lem:coefficients`, with explicit constant `100`. -/
theorem coefficients (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    L.CoefficientEnvelope j := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hj1)
  have hi : i < k := Nat.succ_le_iff.mp hjk
  have hefac : 1 + L.ε ≤ 2 := by linarith [L.epsilon_le_one]
  have hH := norm_nonneg L.H
  have hi0 : (0 : ℝ) ≤ i := by positivity
  have hb := L.beta_bound i (Nat.le_of_lt hi)
  have hbterm : (1 + L.ε) * L.β i ≤ (8 * (i : ℝ)) * ‖L.H‖ := by
    calc
      (1 + L.ε) * L.β i
          ≤ (1 + L.ε) * ((4 * (i : ℝ)) * ‖L.H‖) := by
            exact mul_le_mul_of_nonneg_left hb (by linarith [L.hε_nonneg])
      _ ≤ 2 * ((4 * (i : ℝ)) * ‖L.H‖) := by
            exact mul_le_mul_of_nonneg_right hefac
              (mul_nonneg (by positivity) hH)
      _ = (8 * (i : ℝ)) * ‖L.H‖ := by ring
  have hwraw := L.w_bound_from_beta i hi
  have hw : vnorm (L.w (i + 1)) ≤ (20 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖ := by
    calc
      vnorm (L.w (i + 1))
          ≤ (1 + L.ε) * (2 * ‖L.H‖ + (1 + L.ε) * L.β i) := hwraw
      _ ≤ 2 * (2 * ‖L.H‖ + (8 * (i : ℝ)) * ‖L.H‖) := by
            apply mul_le_mul hefac (add_le_add le_rfl hbterm)
            · exact add_nonneg (mul_nonneg (by norm_num) hH)
                (mul_nonneg (by linarith [L.hε_nonneg])
                  (L.hβ_nonneg i (Nat.le_of_lt hi)))
            · positivity
      _ ≤ (20 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖ := by
            push_cast
            nlinarith
  have hzraw := L.z_relative_bound i hi
  have hz : vnorm (L.z (i + 1)) ≤ (40 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖ := by
    calc
      vnorm (L.z (i + 1)) ≤ (1 + 5 * L.ε) * vnorm (L.w (i + 1)) := hzraw
      _ ≤ 2 * ((20 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖) := by
            apply mul_le_mul (by linarith [L.epsilon_le_one_hundredth]) hw
            · exact vnorm_nonneg _
            · positivity
      _ = (40 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖ := by ring
  have haraw := L.alpha_bound i hi
  have hv := L.vnorm_v_le_two (by omega) hjk
  have ha : |L.α (i + 1)| ≤ (80 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖ := by
    calc
      |L.α (i + 1)|
          ≤ (1 + L.ε) * vnorm (L.v (i + 1)) * vnorm (L.w (i + 1)) := haraw
      _ ≤ 2 * vnorm (L.v (i + 1)) * vnorm (L.w (i + 1)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hefac (vnorm_nonneg _)) (vnorm_nonneg _)
      _ ≤ 2 * 2 * vnorm (L.w (i + 1)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hv (by norm_num)) (vnorm_nonneg _)
      _ ≤ 2 * 2 * ((20 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖) := by
            exact mul_le_mul_of_nonneg_left hw (by norm_num)
      _ = (80 * ((i + 1 : ℕ) : ℝ)) * ‖L.H‖ := by ring
  have hu := L.u_bound i hi
  have hβnext := L.beta_bound (i + 1) hjk
  have hi1 : (1 : ℝ) ≤ (i + 1 : ℕ) := by exact_mod_cast Nat.succ_pos i
  have hscale : 0 ≤ ((i + 1 : ℕ) : ℝ) * ‖L.H‖ :=
    mul_nonneg (by positivity) hH
  constructor
  · exact hu.trans (by
      nlinarith)
  · exact hw.trans (by nlinarith)
  · exact ha.trans (by nlinarith)
  · exact hz.trans (by nlinarith)
  · exact hβnext.trans (by
      nlinarith)

/-- Explicit derived bound for the matrix--vector local error in
`eq:local-u`. -/
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

/-- Explicit derived bound for the update error in `eq:local-w`. -/
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

/-- Explicit derived bound for the scalar product error in `eq:local-alpha`. -/
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

/-- Explicit derived bound for the residual-update error in `eq:local-z`. -/
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

/-- Explicit derived normalization-backward-error bound. -/
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

/-- Explicit recurrence-residual inequality in `thm:local-errors`. -/
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

/-- Near-normalization defect bound in `thm:local-errors`. -/
lemma abs_g_le (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) : |L.g j| ≤ L.ε := by
  rw [g, ← vnorm_sq]
  exact L.hnear j hj1 hjk

/-- Weighted adjacent-product bound in `thm:local-errors`, with explicit
constant `1200 j`. -/
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

/-- `thm:local-errors`, bundled in the same order as the three estimates in
the PDF.  The factors `700 j` and `1200 j` are explicit representatives of
the two suppressed polynomials in the iteration count. -/
theorem local_errors (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    vnorm (L.f j) ≤ (700 * (j : ℝ)) * L.ε * ‖L.H‖ ∧
      |L.g j| ≤ L.ε ∧
      |L.p j| ≤ (1200 * (j : ℝ)) * L.ε * ‖L.H‖ := by
  exact ⟨L.recurrence_error_bound j hj1 hjk, L.abs_g_le j hj1 hjk,
    L.local_product_bound j hj1 hjk⟩

end LanczosRun
end FinitePrecisionLanczos
