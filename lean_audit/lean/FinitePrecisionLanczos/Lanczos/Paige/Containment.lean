import FinitePrecisionLanczos.Core.Spectral










namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)


noncomputable def paigeScale : ℝ := (6000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖


noncomputable def recurrenceScale : ℝ := (700 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖


noncomputable def containmentRadius (t : ℕ) : ℝ :=
  (8 * (t : ℝ) ^ 2 + 5) * L.paigeScale + 3 * L.recurrenceScale

lemma paigeScale_nonneg : 0 ≤ L.paigeScale := by
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by positivity)
      (pow_nonneg (Nat.cast_nonneg k) 3)) L.hε_nonneg)
    (norm_nonneg _)

lemma recurrenceScale_nonneg : 0 ≤ L.recurrenceScale := by
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by positivity)
      (pow_nonneg (Nat.cast_nonneg k) 2)) L.hε_nonneg)
    (norm_nonneg _)


lemma ambient_pos (L : LanczosRun n k) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  have hv : L.v 1 = 0 := by
    funext i
    have hi := i.isLt
    exact False.elim (by omega)
  have hnear := L.hnear 1 (by omega) L.hk_pos
  rw [hv, vnorm_zero] at hnear
  norm_num at hnear
  linarith [L.epsilon_le_one_hundredth]



theorem ritz_norm_identity (y : Vec k) :
    vdot (L.ritzVector y) (L.ritzVector y) =
      vdot y y + 2 * vdot y (L.Rmat *ᵥ y) + vdot y (L.Dmat *ᵥ y) := by
  have hadjoint :
      vdot (L.ritzVector y) (L.ritzVector y) =
        vdot y ((L.Vmatᵀ * L.Vmat) *ᵥ y) := by
    simp only [ritzVector, vdot]
    rw [← Matrix.mulVec_mulVec]
    symm
    exact Matrix.dotProduct_transpose_mulVec L.Vmat y (L.Vmat *ᵥ y)
  have hgram : L.Vmatᵀ * L.Vmat = 1 + L.Omega := by
    simp [Omega]
  rw [hadjoint, hgram, L.gram_split]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, vdot, dotProduct_add]
  have htranspose :
      y ⬝ᵥ L.Rmatᵀ *ᵥ y = y ⬝ᵥ L.Rmat *ᵥ y := by
    rw [Matrix.dotProduct_transpose_mulVec]
  rw [htranspose]
  ring



lemma Dmat_quadratic_lower (y : Vec k) (hy : vdot y y = 1) :
    -L.ε ≤ vdot y (L.Dmat *ᵥ y) := by
  have hdiag := Core.dotProduct_diagonal_mulVec
    (fun j : Fin k => L.g (j.1 + 1)) y
  change -L.ε ≤ y ⬝ᵥ
    (Matrix.diagonal (fun j : Fin k => L.g (j.1 + 1)) *ᵥ y)
  rw [hdiag]
  have hterm : ∀ j : Fin k,
      -L.ε * y j ^ 2 ≤ y j ^ 2 * L.g (j.1 + 1) := by
    intro j
    have hg := L.abs_g_le (j.1 + 1) (by omega) (by omega)
    have hglower : -L.ε ≤ L.g (j.1 + 1) := (abs_le.mp hg).1
    nlinarith [sq_nonneg (y j)]
  have hsum := Finset.sum_le_sum fun j (_hj : j ∈ Finset.univ) => hterm j
  have hsq : ∑ j : Fin k, y j ^ 2 = 1 := by
    simpa [vdot, dotProduct, pow_two] using hy
  calc
    -L.ε = ∑ j : Fin k, -L.ε * y j ^ 2 := by
      rw [← Finset.mul_sum, hsq]
      ring
    _ ≤ ∑ j : Fin k, y j ^ 2 * L.g (j.1 + 1) := hsum
    _ = ∑ j : Fin k, L.g (j.1 + 1) * y j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      ring



lemma ritz_norm_sq_lower (y : Vec k) (hy : vdot y y = 1)
    (hloss : |vdot y (L.Rmat *ᵥ y)| ≤ 3 / 8) :
    1 / 5 ≤ vdot (L.ritzVector y) (L.ritzVector y) := by
  rw [L.ritz_norm_identity y, hy]
  have hrho := (abs_le.mp hloss).1
  have hd := L.Dmat_quadratic_lower y hy
  linarith [L.epsilon_le_one_hundredth]



lemma one_third_le_ritz_vnorm (y : Vec k) (hy : vdot y y = 1)
    (hloss : |vdot y (L.Rmat *ᵥ y)| ≤ 3 / 8) :
    1 / 3 ≤ vnorm (L.ritzVector y) := by
  have hsq := L.ritz_norm_sq_lower y hy hloss
  rw [← vnorm_sq] at hsq
  nlinarith [vnorm_nonneg (L.ritzVector y)]



theorem ritz_rayleigh_identity (y : Vec k) (theta : ℝ)
    (heig : L.Tmat *ᵥ y = theta • y) :
    vdot (L.ritzVector y) (L.H *ᵥ L.ritzVector y) =
      theta * vdot (L.ritzVector y) (L.ritzVector y) +
        vdot (L.ritzVector y) L.rawBoundary * y (lastIndex L.hk_pos) +
        vdot (L.ritzVector y) (L.Fmat *ᵥ y) := by
  have h := congrArg (fun z : Vec n => vdot (L.ritzVector y) z)
    (L.ritz_residual_identity y theta heig)
  simp only [vdot, dotProduct_sub, dotProduct_add, dotProduct_smul,
    smul_eq_mul] at h ⊢
  ring_nf at h ⊢
  linarith



lemma ritz_F_quadratic_bound (y : Vec k) (hy : vdot y y = 1) :
    |vdot (L.ritzVector y) (L.Fmat *ᵥ y)| ≤
      vnorm (L.ritzVector y) * L.recurrenceScale := by
  have hyNorm : vnorm y = 1 := by
    have hsq := vnorm_sq y
    rw [hy] at hsq
    nlinarith [vnorm_nonneg y]
  calc
    |vdot (L.ritzVector y) (L.Fmat *ᵥ y)|
        ≤ vnorm (L.ritzVector y) * vnorm (L.Fmat *ᵥ y) :=
          abs_vdot_le _ _
    _ ≤ vnorm (L.ritzVector y) * (‖L.Fmat‖ * vnorm y) :=
          mul_le_mul_of_nonneg_left (vnorm_mulVec_le L.Fmat y)
            (vnorm_nonneg _)
    _ = vnorm (L.ritzVector y) * ‖L.Fmat‖ := by rw [hyNorm, mul_one]
    _ ≤ vnorm (L.ritzVector y) * L.recurrenceScale :=
          mul_le_mul_of_nonneg_left
            (by simpa [recurrenceScale] using L.Fmat_bound)
            (vnorm_nonneg _)




theorem small_loss_containment (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y)
    (hloss : |vdot y (L.Rmat *ᵥ y)| ≤ 3 / 8) :
    spectralMin L.H - (5 * L.paigeScale + 3 * L.recurrenceScale) ≤ theta ∧
      theta ≤ spectralMax L.H + (5 * L.paigeScale + 3 * L.recurrenceScale) := by
  let x := L.ritzVector y
  let q := vdot x x
  let E := L.paigeScale
  let F := L.recurrenceScale
  have hq : 1 / 5 ≤ q := by
    simpa [x, q] using L.ritz_norm_sq_lower y hy hloss
  have hx : 1 / 3 ≤ vnorm x := by
    simpa [x] using L.one_third_le_ritz_vnorm y hy hloss
  have hqnorm : vnorm x ^ 2 = q := vnorm_sq x
  have hqpos : 0 < q := by linarith
  have hE : 0 ≤ E := L.paigeScale_nonneg
  have hF : 0 ≤ F := L.recurrenceScale_nonneg
  have hboundary :
      |vdot x L.rawBoundary * y (lastIndex L.hk_pos)| ≤ E := by
    simpa [x, E, paigeScale] using L.paige_bound y theta hy heig
  have hFerr : |vdot x (L.Fmat *ᵥ y)| ≤ vnorm x * F := by
    simpa [x, F] using L.ritz_F_quadratic_bound y hy
  have hFabs : vnorm x * F ≤ 3 * F * q := by
    have hx0 := vnorm_nonneg x
    calc
      vnorm x * F = 1 * (vnorm x * F) := by ring
      _ ≤ (3 * vnorm x) * (vnorm x * F) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hx0 hF)
      _ = 3 * F * vnorm x ^ 2 := by ring
      _ = 3 * F * q := by rw [hqnorm]
  have hEabs : E ≤ 5 * E * q := by
    nlinarith
  have hidentity := L.ritz_rayleigh_identity y theta heig
  have herr :
      |vdot x (L.H *ᵥ x) - theta * q| ≤ (5 * E + 3 * F) * q := by
    have hadd := abs_add_le
      (vdot x L.rawBoundary * y (lastIndex L.hk_pos))
      (vdot x (L.Fmat *ᵥ y))
    have hsum :
        |vdot x L.rawBoundary * y (lastIndex L.hk_pos) +
            vdot x (L.Fmat *ᵥ y)| ≤ E + vnorm x * F :=
      hadd.trans (add_le_add hboundary hFerr)
    have hid : vdot x (L.H *ᵥ x) - theta * q =
        vdot x L.rawBoundary * y (lastIndex L.hk_pos) +
          vdot x (L.Fmat *ᵥ y) := by
      dsimp [x, q]
      rw [hidentity]
      ring
    rw [hid]
    calc
      |vdot x L.rawBoundary * y (lastIndex L.hk_pos) +
          vdot x (L.Fmat *ᵥ y)| ≤ E + vnorm x * F := hsum
      _ ≤ 5 * E * q + 3 * F * q := add_le_add hEabs hFabs
      _ = (5 * E + 3 * F) * q := by ring
  have hmin := spectralMin_mul_vdot_le L.ambient_pos L.hHsymm x
  have hmax := vdot_mulVec_le_spectralMax L.ambient_pos L.hHsymm x
  have herrLower := (abs_le.mp herr).1
  have herrUpper := (abs_le.mp herr).2
  constructor <;> dsimp [E, F] at * <;> nlinarith


lemma take_paigeScale_le (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k) :
    (L.take t ht0 htk).paigeScale ≤ L.paigeScale := by
  have htkR : (t : ℝ) ≤ k := by exact_mod_cast htk
  have hcubes : (t : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg t) htkR 3
  have hscale : 0 ≤ L.ε * ‖L.H‖ :=
    mul_nonneg L.hε_nonneg (norm_nonneg _)
  simp only [paigeScale, take_epsilon, take_H]
  nlinarith


lemma take_recurrenceScale_le (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k) :
    (L.take t ht0 htk).recurrenceScale ≤ L.recurrenceScale := by
  have htkR : (t : ℝ) ≤ k := by exact_mod_cast htk
  have hsquares : (t : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg t) htkR 2
  have hscale : 0 ≤ L.ε * ‖L.H‖ :=
    mul_nonneg L.hε_nonneg (norm_nonneg _)
  simp only [recurrenceScale, take_epsilon, take_H]
  nlinarith





theorem containment_prefix :
    ∀ (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k) (y : Vec t) (theta : ℝ),
      vdot y y = 1 → (L.take t ht0 htk).Tmat *ᵥ y = theta • y →
      spectralMin L.H - L.containmentRadius t ≤ theta ∧
        theta ≤ spectralMax L.H + L.containmentRadius t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro ht0 htk y theta hy heig
      let P := L.take t ht0 htk
      by_cases hloss : |vdot y (P.Rmat *ᵥ y)| ≤ 3 / 8
      · have hsmall := P.small_loss_containment y theta hy heig hloss
        simp only [P, take_H] at hsmall
        have hE := L.take_paigeScale_le t ht0 htk
        have hF := L.take_recurrenceScale_le t ht0 htk
        have hEt : 0 ≤ L.paigeScale := L.paigeScale_nonneg
        have hFt : 0 ≤ L.recurrenceScale := L.recurrenceScale_nonneg
        have htR : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
        have hradius :
            5 * P.paigeScale + 3 * P.recurrenceScale ≤
              L.containmentRadius t := by
          dsimp [containmentRadius]
          nlinarith
        simpa [P, take_H] using
          And.intro
            (show spectralMin L.H - L.containmentRadius t ≤ theta by
              linarith [hsmall.1])
            (show theta ≤ spectralMax L.H + L.containmentRadius t by
              linarith [hsmall.2])
      · have hloss' : 3 / 8 < |vdot y (P.Rmat *ᵥ y)| := lt_of_not_ge hloss
        obtain ⟨s, r, hgap, _hedge⟩ :=
          L.paige_descent t ht0 htk y theta hy heig hloss'
        let ts := prefixLength s
        let ys := L.prefixEigenvector t ht0 htk s r
        let thetas := L.prefixEigenvalue t ht0 htk s r
        have hts0 : 0 < ts := prefixLength_pos s
        have htst : ts < t := prefixLength_lt s
        have htsk : ts ≤ k := htst.le.trans htk
        have hprev := ih ts htst hts0 htsk ys thetas
          (L.prefixEigenvector_unit t ht0 htk s r)
          (L.prefixEigenvector_equation t ht0 htk s r)
        have hE : 0 ≤ L.paigeScale := L.paigeScale_nonneg
        have hF : 0 ≤ L.recurrenceScale := L.recurrenceScale_nonneg
        have hcast : (ts : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast htst
        have htsR : 0 ≤ (ts : ℝ) := Nat.cast_nonneg _
        have hcoef :
            8 * (ts : ℝ) ^ 2 + 5 + 8 * (t : ℝ) ≤
              8 * (t : ℝ) ^ 2 + 5 := by
          nlinarith
        have hradius :
            L.containmentRadius ts + 8 * (t : ℝ) * L.paigeScale ≤
              L.containmentRadius t := by
          dsimp [containmentRadius]
          have hm := mul_le_mul_of_nonneg_right hcoef hE
          nlinarith
        have hgap' : |theta - thetas| ≤ 8 * (t : ℝ) * L.paigeScale := by
          simpa [thetas, paigeScale] using hgap
        have hgapLower := (abs_le.mp hgap').1
        have hgapUpper := (abs_le.mp hgap').2
        constructor
        · linarith [hprev.1]
        · linarith [hprev.2]


theorem containment (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y) :
    spectralMin L.H - L.containmentRadius k ≤ theta ∧
      theta ≤ spectralMax L.H + L.containmentRadius k := by
  simpa using L.containment_prefix k L.hk_pos le_rfl y theta hy heig




theorem containment_eigenvalue (i : Fin k) :
    spectralMin L.H - L.containmentRadius k ≤
        (isHermitian_of_transpose_eq L.Tmat_transpose).eigenvalues i ∧
      (isHermitian_of_transpose_eq L.Tmat_transpose).eigenvalues i ≤
        spectralMax L.H + L.containmentRadius k := by
  let hT := isHermitian_of_transpose_eq L.Tmat_transpose
  let y : Vec k := ⇑(hT.eigenvectorBasis i)
  have hy : vdot y y = 1 := by
    rw [← vnorm_sq]
    change ‖hT.eigenvectorBasis i‖ ^ 2 = 1
    rw [hT.eigenvectorBasis.orthonormal.1 i]
    norm_num
  have heig : L.Tmat *ᵥ y = hT.eigenvalues i • y :=
    hT.mulVec_eigenvectorBasis i
  exact L.containment y (hT.eigenvalues i) hy heig

end LanczosRun
end FinitePrecisionLanczos
