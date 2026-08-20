import FinitePrecisionLanczos.Core.Measure.SpectralMass

/-!
# Finite transport and the cluster cut estimate

This is the finite, elementary part of the cluster-mass extension.  It is stated on
finite atom index types, so repeated atoms cause no difficulty.  The only
input is a coupling and a lower bound on the distance of every pair crossing
the selected cut.
-/

namespace FinitePrecisionLanczos

/-- A nonnegative finite coupling with prescribed row and column masses. -/
structure FiniteCoupling {I J : Type*} [Fintype I] [Fintype J]
    (source : I → ℝ) (target : J → ℝ) where
  weight : I → J → ℝ
  nonneg : ∀ i j, 0 ≤ weight i j
  row_sum : ∀ i, ∑ j, weight i j = source i
  column_sum : ∀ j, ∑ i, weight i j = target j

/-- Cost of a coupling between atoms at `x i` and `y j`. -/
noncomputable def FiniteCoupling.cost {I J : Type*} [Fintype I] [Fintype J]
    {source : I → ℝ} {target : J → ℝ}
    (π : FiniteCoupling source target) (x : I → ℝ) (y : J → ℝ) : ℝ :=
  ∑ i, ∑ j, π.weight i j * |x i - y j|

/-- Total mass whose atom location satisfies a predicate. -/
noncomputable def finiteGroupMass {I : Type*} [Fintype I]
    (weight : I → ℝ) (x : I → ℝ) (G : ℝ → Prop) [DecidablePred G] : ℝ :=
  ∑ i, (if G (x i) then 1 else 0) * weight i

/-- Difference of group masses is the signed coupling mass across the cut. -/
lemma groupMass_sub_eq_coupling_sum
    {I J : Type*} [Fintype I] [Fintype J]
    {source : I → ℝ} {target : J → ℝ}
    (π : FiniteCoupling source target)
    (x : I → ℝ) (y : J → ℝ)
    (G C : ℝ → Prop) [DecidablePred G] [DecidablePred C] :
    finiteGroupMass source x G - finiteGroupMass target y C =
      ∑ i, ∑ j, π.weight i j *
        ((if G (x i) then 1 else 0) - (if C (y j) then 1 else 0)) := by
  unfold finiteGroupMass
  simp_rw [← π.row_sum, ← π.column_sum]
  simp_rw [Finset.mul_sum]
  simp_rw [mul_sub]
  simp_rw [Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun j i =>
    (if C (y j) then 1 else 0) * π.weight i j)]
  apply congrArg₂ (· - ·)
  · apply Fintype.sum_congr
    intro i
    apply Fintype.sum_congr
    intro j
    ring
  · apply Fintype.sum_congr
    intro i
    apply Fintype.sum_congr
    intro j
    ring

/-- Absolute value of a finite double sum is bounded by the sum of the
absolute values. -/
lemma abs_double_sum_le_sum_abs {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℝ) :
    |∑ i, ∑ j, a i j| ≤ ∑ i, ∑ j, |a i j| := by
  calc
    |∑ i, ∑ j, a i j| ≤ ∑ i, |∑ j, a i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |a i j| := by
      apply Finset.sum_le_sum
      intro i _hi
      exact Finset.abs_sum_le_sum_abs _ _

/-- The cut/crossing estimate used for separated cluster masses.

If every source--target pair lying on opposite sides of the selected group
cut travels at least `r`, then the group-mass discrepancy times `r` is no
larger than the transport cost. -/
theorem finiteCoupling_cluster_cut
    {I J : Type*} [Fintype I] [Fintype J]
    {source : I → ℝ} {target : J → ℝ}
    (π : FiniteCoupling source target)
    (x : I → ℝ) (y : J → ℝ)
    (G C : ℝ → Prop) [DecidablePred G] [DecidablePred C]
    (r : ℝ) (hr : 0 ≤ r)
    (hcross : ∀ i j,
      (G (x i) ∧ ¬C (y j)) ∨ (¬G (x i) ∧ C (y j)) →
        r ≤ |x i - y j|) :
    r * |finiteGroupMass source x G - finiteGroupMass target y C| ≤
      π.cost x y := by
  let a : I → J → ℝ := fun i j => π.weight i j *
    ((if G (x i) then 1 else 0) - (if C (y j) then 1 else 0))
  have hmass :
      finiteGroupMass source x G - finiteGroupMass target y C =
        ∑ i, ∑ j, a i j := by
    exact groupMass_sub_eq_coupling_sum π x y G C
  have habs : |∑ i, ∑ j, a i j| ≤ ∑ i, ∑ j, |a i j| :=
    abs_double_sum_le_sum_abs a
  have hterm : ∀ i j,
      r * |a i j| ≤ π.weight i j * |x i - y j| := by
    intro i j
    have hp := π.nonneg i j
    by_cases hG : G (x i) <;> by_cases hC : C (y j)
    · simpa [a, hG, hC] using
        (mul_nonneg hp (abs_nonneg (x i - y j)))
    · have hs := hcross i j (Or.inl ⟨hG, hC⟩)
      simpa [a, hG, hC, abs_of_nonneg hp, mul_comm] using
        (mul_le_mul_of_nonneg_left hs hp)
    · have hs := hcross i j (Or.inr ⟨hG, hC⟩)
      simpa [a, hG, hC, abs_of_nonneg hp, mul_comm] using
        (mul_le_mul_of_nonneg_left hs hp)
    · simpa [a, hG, hC] using
        (mul_nonneg hp (abs_nonneg (x i - y j)))
  rw [hmass]
  calc
    r * |∑ i, ∑ j, a i j| ≤ r * ∑ i, ∑ j, |a i j| :=
      mul_le_mul_of_nonneg_left habs hr
    _ = ∑ i, ∑ j, r * |a i j| := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, π.weight i j * |x i - y j| := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      exact hterm i j
    _ = π.cost x y := rfl

end FinitePrecisionLanczos
