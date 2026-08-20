import FinitePrecisionLanczos.Lanczos.Paige.Prefix

/-!
# Scalar core of Paige descent

This is the finite selection argument in `lem:descent`.  The surrounding
matrix lemmas only have to supply the three exact PDF formulas
`eq:leading-coefficient`, `eq:rho-expansion`, and
`eq:leading-paige-product`, together with the displayed aggregate
Cauchy--Schwarz bound.  Keeping this finite scalar argument separate makes
the contradiction and its constant `3/8` directly auditable.
-/

namespace FinitePrecisionLanczos

/-- Reindex the strict upper triangle by its nonzero columns.  This is the
finite-index bookkeeping behind the first equality of `eq:rho-expansion`. -/
lemma strictUpper_sum_by_columns {t : ℕ} (f : Fin t → Fin t → ℝ) :
    (∑ i : Fin t, ∑ j : Fin t, if i.1 < j.1 then f i j else 0) =
      ∑ s : Fin (t - 1), ∑ r : Fin (s.1 + 1),
        f ⟨r.1, lt_trans r.2 (by omega : s.1 + 1 < t)⟩
          ⟨s.1 + 1, by omega⟩ := by
  induction t with
  | zero => simp
  | succ t ih =>
      cases t with
      | zero => simp
      | succ q =>
          rw [Finset.sum_comm]
          let fsmall : Fin (q + 1) → Fin (q + 1) → ℝ :=
            fun i j => f i.castSucc j.castSucc
          have hsmall := ih fsmall
          let col : Fin (q + 2) → ℝ := fun j =>
            ∑ i : Fin (q + 2), if i.1 < j.1 then f i j else 0
          let rhscol : Fin (q + 1) → ℝ := fun s =>
            ∑ r : Fin (s.1 + 1),
              f ⟨r.1, lt_trans r.2 (by omega : s.1 + 1 < q + 2)⟩
                ⟨s.1 + 1, by omega⟩
          change (∑ j, col j) = ∑ s, rhscol s
          rw [Fin.sum_univ_castSucc col, Fin.sum_univ_castSucc rhscol]
          apply congrArg₂ (.+.)
          · calc
              ∑ j : Fin (q + 1), col j.castSucc
                  = ∑ j : Fin (q + 1), ∑ i : Fin (q + 1),
                      if i.1 < j.1 then fsmall i j else 0 := by
                    apply Finset.sum_congr rfl
                    intro j _
                    change (∑ i : Fin (q + 2),
                      if i.1 < j.castSucc.1 then f i j.castSucc else 0) = _
                    rw [Fin.sum_univ_castSucc]
                    simp [fsmall]
              _ = ∑ s : Fin q, ∑ r : Fin (s.1 + 1),
                    fsmall ⟨r.1, lt_trans r.2 (by omega : s.1 + 1 < q + 1)⟩
                      ⟨s.1 + 1, by omega⟩ := by
                    rw [Finset.sum_comm]
                    exact hsmall
              _ = ∑ s : Fin q, rhscol s.castSucc := by
                    apply Finset.sum_congr rfl
                    intro s _
                    simp only [rhscol, fsmall, Fin.val_castSucc]
                    apply Finset.sum_congr rfl
                    intro r _
                    congr 2 <;> apply Fin.ext <;> rfl
          · simp only [col, rhscol, Fin.val_last, Fin.sum_univ_castSucc,
              Fin.val_castSucc]
            simp
            apply congrArg₂ (.+.)
            · apply Finset.sum_congr rfl
              intro r _
              congr 2 <;> apply Fin.ext <;> simp
            · congr 2 <;> apply Fin.ext <;> simp

/-- The scalar selection argument at the heart of `lem:descent`, for a
strictly positive uniform Paige error.  The index `s : Fin (t-1)` represents
the paper's prefix length `s+1`, and `r : Fin (s+1)` its Ritz index. -/
theorem paige_descent_selection_positive
    {t : ℕ} (ht : 0 < t) (E rho : ℝ) (hE : 0 < E)
    (gap edge coeff corr : (s : Fin (t - 1)) → Fin (s.1 + 1) → ℝ)
    (tail : Fin (t - 1) → ℝ)
    (hcoeff : ∀ s r,
      gap s r * coeff s r = edge s r * tail s)
    (hpaige : ∀ s r, |edge s r * corr s r| ≤ E)
    (hrho : rho = ∑ s, ∑ r, coeff s r * corr s r * tail s)
    (haggregate :
      (∑ s, ∑ r, ((tail s) ^ 2 + |coeff s r * tail s|))
        ≤ (2 : ℝ) * t)
    (hloss : (3 / 8 : ℝ) < |rho|) :
    ∃ s r,
      |gap s r| ≤ 8 * t * E ∧ |edge s r| ≤ 8 * t * E := by
  let psi : ℝ := 8 * t * E
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hpsi : 0 < psi := by dsimp [psi]; positivity
  by_contra hnone
  push Not at hnone
  have hterm : ∀ s r,
      |coeff s r * corr s r * tail s| ≤
        (E / psi) * ((tail s) ^ 2 + |coeff s r * tail s|) := by
    intro s r
    have halt : psi < |gap s r| ∨ psi < |edge s r| := by
      by_cases h : psi < |gap s r|
      · exact Or.inl h
      · exact Or.inr (hnone s r (by simpa [psi] using le_of_not_gt h))
    have hc0 : 0 ≤ |coeff s r| := abs_nonneg _
    have hr0 : 0 ≤ |corr s r| := abs_nonneg _
    have hy0 : 0 ≤ |tail s| := abs_nonneg _
    have hpsi0 : 0 ≤ psi := hpsi.le
    have hEpsi : 0 ≤ E / psi := div_nonneg hE.le hpsi.le
    have hcoeffAbs :
        |gap s r| * |coeff s r| = |edge s r| * |tail s| := by
      simpa [abs_mul] using congrArg abs (hcoeff s r)
    have hpaigeAbs : |edge s r| * |corr s r| ≤ E := by
      simpa [abs_mul] using hpaige s r
    rw [abs_mul, abs_mul]
    rcases halt with hgap | hedge
    · have hmul :
          psi * (|coeff s r| * |corr s r| * |tail s|) ≤
            E * |tail s| ^ 2 := by
        calc
          psi * (|coeff s r| * |corr s r| * |tail s|)
              ≤ |gap s r| * (|coeff s r| * |corr s r| * |tail s|) :=
                mul_le_mul_of_nonneg_right hgap.le
                  (mul_nonneg (mul_nonneg hc0 hr0) hy0)
          _ = (|gap s r| * |coeff s r|) * |corr s r| * |tail s| := by ring
          _ = (|edge s r| * |tail s|) * |corr s r| * |tail s| := by
                rw [hcoeffAbs]
          _ = (|edge s r| * |corr s r|) * |tail s| ^ 2 := by ring
          _ ≤ E * |tail s| ^ 2 :=
                mul_le_mul_of_nonneg_right hpaigeAbs (sq_nonneg _)
        
      have hspecific :
          |coeff s r| * |corr s r| * |tail s| ≤
            (E / psi) * (tail s) ^ 2 := by
        rw [show (E / psi) * (tail s) ^ 2 =
          (E * (tail s) ^ 2) / psi by field_simp]
        apply (le_div_iff₀ hpsi).2
        simpa [sq_abs, mul_comm] using hmul
      exact hspecific.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (abs_nonneg (coeff s r * tail s))) hEpsi)
    · have hcorr : |corr s r| ≤ E / psi := by
        apply (le_div_iff₀ hpsi).2
        calc
          |corr s r| * psi ≤ |corr s r| * |edge s r| :=
            mul_le_mul_of_nonneg_left hedge.le hr0
          _ = |edge s r| * |corr s r| := by ring
          _ ≤ E := hpaigeAbs
      have hspecific :
          |coeff s r| * |corr s r| * |tail s| ≤
            (E / psi) * |coeff s r * tail s| := by
        rw [abs_mul]
        calc
          |coeff s r| * |corr s r| * |tail s|
              ≤ |coeff s r| * (E / psi) * |tail s| := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hcorr hc0) hy0
          _ = (E / psi) * (|coeff s r| * |tail s|) := by ring
      exact hspecific.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (sq_nonneg (tail s))) hEpsi)
  have hrhoBound :
      |rho| ≤ (E / psi) * 2 * t := by
    rw [hrho]
    calc
      |∑ s, ∑ r, coeff s r * corr s r * tail s|
          ≤ ∑ s, |∑ r, coeff s r * corr s r * tail s| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, ∑ r, |coeff s r * corr s r * tail s| := by
            apply Finset.sum_le_sum
            intro s _
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, ∑ r,
          (E / psi) * ((tail s) ^ 2 + |coeff s r * tail s|) := by
            apply Finset.sum_le_sum
            intro s _
            apply Finset.sum_le_sum
            intro r _
            exact hterm s r
      _ = (E / psi) *
          (∑ s, ∑ r, ((tail s) ^ 2 + |coeff s r * tail s|)) := by
            simp_rw [Finset.mul_sum]
      _ ≤ (E / psi) * (2 * t) :=
            mul_le_mul_of_nonneg_left haggregate (div_nonneg hE.le hpsi.le)
      _ = (E / psi) * 2 * t := by ring
  have hratio : (E / psi) * 2 * t = 1 / 4 := by
    dsimp [psi]
    field_simp
    ring
  rw [hratio] at hrhoBound
  norm_num at hloss hrhoBound
  linarith

/-- Full scalar descent selection, including the exact-arithmetic case
`E = 0` treated separately in the proof of `lem:descent`. -/
theorem paige_descent_selection
    {t : ℕ} (ht : 0 < t) (E rho : ℝ) (hE : 0 ≤ E)
    (gap edge coeff corr : (s : Fin (t - 1)) → Fin (s.1 + 1) → ℝ)
    (tail : Fin (t - 1) → ℝ)
    (hcoeff : ∀ s r,
      gap s r * coeff s r = edge s r * tail s)
    (hpaige : ∀ s r, |edge s r * corr s r| ≤ E)
    (hrho : rho = ∑ s, ∑ r, coeff s r * corr s r * tail s)
    (haggregate :
      (∑ s, ∑ r, ((tail s) ^ 2 + |coeff s r * tail s|))
        ≤ (2 : ℝ) * t)
    (hloss : (3 / 8 : ℝ) < |rho|) :
    ∃ s r,
      |gap s r| ≤ 8 * t * E ∧ |edge s r| ≤ 8 * t * E := by
  rcases hE.eq_or_lt with rfl | hEpos
  · have hzeroProduct : ∀ s r,
        gap s r ≠ 0 ∨ edge s r ≠ 0 →
          coeff s r * corr s r * tail s = 0 := by
      intro s r hne
      have hp : edge s r * corr s r = 0 := by
        have := hpaige s r
        simpa using (abs_eq_zero.mp (le_antisymm this (abs_nonneg _)))
      rcases hne with hgap | hedge
      · by_cases he : edge s r = 0
        · have hc : coeff s r = 0 := by
            have hi := hcoeff s r
            rw [he, zero_mul] at hi
            exact (mul_eq_zero.mp hi).resolve_left hgap
          simp [hc]
        · have hr : corr s r = 0 := (mul_eq_zero.mp hp).resolve_left he
          simp [hr]
      · have hr : corr s r = 0 := (mul_eq_zero.mp hp).resolve_left hedge
        simp [hr]
    by_contra hnone
    push Not at hnone
    have hall : ∀ s r, coeff s r * corr s r * tail s = 0 := by
      intro s r
      apply hzeroProduct s r
      by_cases hg : gap s r = 0
      · right
        intro he
        have hboth : |gap s r| ≤ 8 * (t : ℝ) * 0 ∧
            |edge s r| ≤ 8 * (t : ℝ) * 0 := by simp [hg, he]
        exact (not_le_of_gt (hnone s r hboth.1)) hboth.2
      · exact Or.inl hg
    have hrho0 : rho = 0 := by
      rw [hrho]
      simp_rw [hall]
      simp
    rw [hrho0, abs_zero] at hloss
    norm_num at hloss
  · exact paige_descent_selection_positive ht E rho hEpos gap edge coeff corr tail
      hcoeff hpaige hrho haggregate hloss

end FinitePrecisionLanczos
