import FinitePrecisionLanczos.Lanczos.Paige.Containment









namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)



noncomputable def iterationScale : ℝ := 8 * (k : ℝ) * L.paigeScale

lemma iterationScale_nonneg : 0 ≤ L.iterationScale := by
  exact mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
    L.paigeScale_nonneg


lemma prefix_iterationScale_le (t : ℕ) (htk : t ≤ k) :
    8 * (t : ℝ) * L.paigeScale ≤ L.iterationScale := by
  have htkR : (t : ℝ) ≤ k := by exact_mod_cast htk
  have hE := L.paigeScale_nonneg
  dsimp [iterationScale]
  nlinarith



lemma two_fifths_le_ritz_vnorm (y : Vec k) (hy : vdot y y = 1)
    (hloss : |vdot y (L.Rmat *ᵥ y)| ≤ 3 / 8) :
    2 / 5 ≤ vnorm (L.ritzVector y) := by
  have hsq := L.ritz_norm_sq_lower y hy hloss
  rw [← vnorm_sq] at hsq
  nlinarith [vnorm_nonneg (L.ritzVector y)]


theorem small_loss_localization (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y)
    (hloss : |vdot y (L.Rmat *ᵥ y)| ≤ 3 / 8) :
    spectralDistance L.H theta ≤
      3 * (L.β k * |y (lastIndex L.hk_pos)|) + 3 * L.recurrenceScale := by
  let x := L.ritzVector y
  let r := L.β k * |y (lastIndex L.hk_pos)|
  let F := L.recurrenceScale
  let d := spectralDistance L.H theta
  have hr : 0 ≤ r := mul_nonneg (L.hβ_nonneg k le_rfl) (abs_nonneg _)
  have hF : 0 ≤ F := L.recurrenceScale_nonneg
  have hd : 0 ≤ d := spectralDistance_nonneg L.ambient_pos
    (isHermitian_of_transpose_eq L.hHsymm) theta
  have hx : 2 / 5 ≤ vnorm x := by
    simpa [x] using L.two_fifths_le_ritz_vnorm y hy hloss
  have hxpos : 0 < vnorm x := by linarith
  have hsqrt : Real.sqrt (1 + L.ε) ≤ 11 / 10 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · have he := L.epsilon_le_one_hundredth
      nlinarith
  have hres := L.ritz_residual_bound y theta hy heig
  have hres' : vnorm (L.H *ᵥ x - theta • x) ≤ 11 / 10 * r + F := by
    calc
      vnorm (L.H *ᵥ x - theta • x)
          ≤ Real.sqrt (1 + L.ε) * r + ‖L.Fmat‖ := by
            simpa [x, r, mul_assoc] using hres
      _ ≤ 11 / 10 * r + F := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hsqrt hr)
          (by simpa [F, recurrenceScale] using L.Fmat_bound)
  have hdist : d * vnorm x ≤ vnorm (L.H *ᵥ x - theta • x) := by
    simpa [d, x] using
      spectralDistance_mul_vnorm_le_residual L.ambient_pos L.hHsymm theta x
  have hbase : 11 / 10 * r + F ≤ (3 * r + 3 * F) * vnorm x := by
    have hfirst : 11 / 10 * r + F ≤ (2 / 5) * (3 * r + 3 * F) := by
      nlinarith
    have hsecond : (2 / 5) * (3 * r + 3 * F) ≤
        vnorm x * (3 * r + 3 * F) :=
      mul_le_mul_of_nonneg_right hx (by positivity)
    calc
      11 / 10 * r + F ≤ (2 / 5) * (3 * r + 3 * F) := hfirst
      _ ≤ vnorm x * (3 * r + 3 * F) := hsecond
      _ = (3 * r + 3 * F) * vnorm x := by ring
  have hfinal : d ≤ 3 * r + 3 * F := by
    by_contra hnot
    have hstrict : 3 * r + 3 * F < d := lt_of_not_ge hnot
    have hmul := mul_lt_mul_of_pos_right hstrict hxpos
    linarith
  simpa [d, r, F] using hfinal



theorem stabilized_prefix :
    ∀ (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k) (y : Vec t) (theta : ℝ),
      vdot y y = 1 → (L.take t ht0 htk).Tmat *ᵥ y = theta • y →
      spectralDistance L.H theta ≤
        ((t - 1 : ℕ) : ℝ) * L.iterationScale +
          3 * max ((L.take t ht0 htk).β t *
            |y (lastIndex (L.take t ht0 htk).hk_pos)|) L.iterationScale +
          3 * L.recurrenceScale := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro ht0 htk y theta hy heig
      let P := L.take t ht0 htk
      let rnow := P.β t * |y (lastIndex P.hk_pos)|
      by_cases hloss : |vdot y (P.Rmat *ᵥ y)| ≤ 3 / 8
      · have hsmall := P.small_loss_localization y theta hy heig hloss
        simp only [P, take_H] at hsmall
        change spectralDistance L.H theta ≤
          3 * rnow + 3 * (L.take t ht0 htk).recurrenceScale at hsmall
        have hF := L.take_recurrenceScale_le t ht0 htk
        have hiter := L.iterationScale_nonneg
        have hmax : rnow ≤ max rnow L.iterationScale := le_max_left _ _
        have hnat : 0 ≤ (((t - 1 : ℕ) : ℝ)) := Nat.cast_nonneg _
        have hF0 := L.recurrenceScale_nonneg
        change spectralDistance L.H theta ≤
          ((t - 1 : ℕ) : ℝ) * L.iterationScale +
            3 * max rnow L.iterationScale + 3 * L.recurrenceScale
        nlinarith
      · have hloss' : 3 / 8 < |vdot y (P.Rmat *ᵥ y)| := lt_of_not_ge hloss
        obtain ⟨s, j, hgap, hedge⟩ :=
          L.paige_descent t ht0 htk y theta hy heig hloss'
        let ts := prefixLength s
        let ys := L.prefixEigenvector t ht0 htk s j
        let thetas := L.prefixEigenvalue t ht0 htk s j
        let Ps := L.descentPrefix t ht0 htk s
        let rprev := Ps.β ts * |ys (lastIndex Ps.hk_pos)|
        have hts0 : 0 < ts := prefixLength_pos s
        have htst : ts < t := prefixLength_lt s
        have htsk : ts ≤ k := htst.le.trans htk
        have hprev := ih ts htst hts0 htsk ys thetas
          (L.prefixEigenvector_unit t ht0 htk s j)
          (L.prefixEigenvector_equation t ht0 htk s j)
        have hpsi_t := L.prefix_iterationScale_le t htk
        have hgap' : |theta - thetas| ≤ L.iterationScale := by
          have hgapBase : |theta - thetas| ≤ 8 * (t : ℝ) * L.paigeScale := by
            simpa [thetas, paigeScale] using hgap
          exact hgapBase.trans hpsi_t
        have hrprev : rprev ≤ L.iterationScale := by
          have hedge' : rprev ≤ 8 * (t : ℝ) * L.paigeScale := by
            simpa [rprev, Ps, ts, ys, descentPrefix, lastIndex, paigeScale]
              using hedge
          exact hedge'.trans hpsi_t
        have hprev' : spectralDistance L.H thetas ≤
            ((ts - 1 : ℕ) : ℝ) * L.iterationScale +
              3 * L.iterationScale + 3 * L.recurrenceScale := by
          have hmaxPrev : max rprev L.iterationScale = L.iterationScale :=
            max_eq_right hrprev
          change spectralDistance L.H thetas ≤
            ((ts - 1 : ℕ) : ℝ) * L.iterationScale +
              3 * max rprev L.iterationScale + 3 * L.recurrenceScale at hprev
          rw [hmaxPrev] at hprev
          exact hprev
        have htri := spectralDistance_triangle L.ambient_pos
          (isHermitian_of_transpose_eq L.hHsymm) theta thetas
        have hstepNat : ts - 1 + 1 ≤ t - 1 := by omega
        have hstepCast : (((ts - 1 + 1 : ℕ) : ℝ)) ≤ ((t - 1 : ℕ) : ℝ) := by
          exact_mod_cast hstepNat
        have hiter0 := L.iterationScale_nonneg
        have hsteps :
            ((ts - 1 : ℕ) : ℝ) * L.iterationScale + L.iterationScale ≤
              ((t - 1 : ℕ) : ℝ) * L.iterationScale := by
          have hm := mul_le_mul_of_nonneg_right hstepCast hiter0
          calc
            ((ts - 1 : ℕ) : ℝ) * L.iterationScale + L.iterationScale =
                ((((ts - 1 : ℕ) : ℝ)) + 1) * L.iterationScale := by ring
            _ ≤ ((t - 1 : ℕ) : ℝ) * L.iterationScale := by
              norm_num at hm
              exact hm
        have hmaxNow : L.iterationScale ≤ max rnow L.iterationScale :=
          le_max_right _ _
        have hgapUpper := hgap'
        change spectralDistance L.H theta ≤
          ((t - 1 : ℕ) : ℝ) * L.iterationScale +
            3 * max rnow L.iterationScale + 3 * L.recurrenceScale
        linarith


theorem stabilized_max_form (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y) :
    spectralDistance L.H theta ≤
      ((k - 1 : ℕ) : ℝ) * L.iterationScale +
        3 * max (L.β k * |y (lastIndex L.hk_pos)|) L.iterationScale +
        3 * L.recurrenceScale := by
  simpa using L.stabilized_prefix k L.hk_pos le_rfl y theta hy heig




theorem stabilized (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y) :
    spectralDistance L.H theta ≤
      3 * (L.β k * |y (lastIndex L.hk_pos)|) +
        (((k - 1 : ℕ) : ℝ) + 3) * L.iterationScale +
        3 * L.recurrenceScale := by
  let r := L.β k * |y (lastIndex L.hk_pos)|
  have hr : 0 ≤ r := mul_nonneg (L.hβ_nonneg k le_rfl) (abs_nonneg _)
  have hiter := L.iterationScale_nonneg
  have hmax : max r L.iterationScale ≤ r + L.iterationScale := by
    exact max_le (le_add_of_nonneg_right hiter) (le_add_of_nonneg_left hr)
  have h := L.stabilized_max_form y theta hy heig
  change spectralDistance L.H theta ≤
    ((k - 1 : ℕ) : ℝ) * L.iterationScale +
      3 * max r L.iterationScale + 3 * L.recurrenceScale at h
  change spectralDistance L.H theta ≤
    3 * r + (((k - 1 : ℕ) : ℝ) + 3) * L.iterationScale +
      3 * L.recurrenceScale
  nlinarith


theorem stabilized_of_boundary_le (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y)
    (hboundary : L.β k * |y (lastIndex L.hk_pos)| ≤ L.iterationScale) :
    spectralDistance L.H theta ≤
      ((k - 1 : ℕ) : ℝ) * L.iterationScale +
        3 * L.iterationScale + 3 * L.recurrenceScale := by
  simpa [max_eq_right hboundary] using L.stabilized_max_form y theta hy heig


theorem terminal_localization (hterminal : L.β k = 0) (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y) :
    spectralDistance L.H theta ≤
      ((k - 1 : ℕ) : ℝ) * L.iterationScale +
        3 * L.iterationScale + 3 * L.recurrenceScale := by
  have h := L.stabilized y theta hy heig
  rw [hterminal, zero_mul] at h
  convert h using 1 <;> ring



theorem terminal_localization_eigenvalue (hterminal : L.β k = 0) (i : Fin k) :
    spectralDistance L.H
        ((isHermitian_of_transpose_eq L.Tmat_transpose).eigenvalues i) ≤
      ((k - 1 : ℕ) : ℝ) * L.iterationScale +
        3 * L.iterationScale + 3 * L.recurrenceScale := by
  let hT := isHermitian_of_transpose_eq L.Tmat_transpose
  let y : Vec k := ⇑(hT.eigenvectorBasis i)
  have hy : vdot y y = 1 := by
    rw [← vnorm_sq]
    change ‖hT.eigenvectorBasis i‖ ^ 2 = 1
    rw [hT.eigenvectorBasis.orthonormal.1 i]
    norm_num
  have heig : L.Tmat *ᵥ y = hT.eigenvalues i • y :=
    hT.mulVec_eigenvectorBasis i
  exact L.terminal_localization hterminal y (hT.eigenvalues i) hy heig

end LanczosRun
end FinitePrecisionLanczos
