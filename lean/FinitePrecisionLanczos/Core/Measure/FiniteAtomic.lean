import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Finite atomic measures are determined by their moments

This elementary lemma closes the logical step used after
`greenbaum_starting_moment`: equality of all moments is equality of the
underlying finite atomic spectral measures.  It is proved by a Lagrange
polynomial on the finite union of the two supports.
-/

namespace FinitePrecisionLanczos

open Polynomial

/-- A finitely supported signed mass function. -/
abbrev AtomicMass := ℝ →₀ ℝ

/-- Its `m`-th moment. -/
noncomputable def atomicMoment (μ : AtomicMass) (m : ℕ) : ℝ :=
  μ.sum fun x w => w * x ^ m

@[simp] lemma atomicMoment_zero (m : ℕ) : atomicMoment 0 m = 0 := by
  simp [atomicMoment]

@[simp] lemma atomicMoment_add (μ ν : AtomicMass) (m : ℕ) :
    atomicMoment (μ + ν) m = atomicMoment μ m + atomicMoment ν m := by
  classical
  unfold atomicMoment
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

@[simp] lemma atomicMoment_single (x w : ℝ) (m : ℕ) :
    atomicMoment (Finsupp.single x w) m = w * x ^ m := by
  classical
  simp [atomicMoment]

/-- Vanishing monomial moments imply vanishing against every polynomial on
the same finite support. -/
lemma polynomial_sum_eq_zero_of_moments
    (S : Finset ℝ) (w : ℝ → ℝ)
    (hmom : ∀ m : ℕ, ∑ x ∈ S, w x * x ^ m = 0)
    (p : ℝ[X]) : ∑ x ∈ S, w x * p.eval x = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp_rw [Polynomial.eval_add, mul_add]
      rw [Finset.sum_add_distrib]
      linarith
  | monomial m c =>
      simp_rw [Polynomial.eval_monomial]
      calc
        ∑ x ∈ S, w x * (c * x ^ m) =
            c * ∑ x ∈ S, w x * x ^ m := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _hx
          ring
        _ = 0 := by rw [hmom m, mul_zero]

/-- A signed mass supported on a finite set and having all moments zero is
identically zero. -/
theorem finite_support_eq_zero_of_moments
    (S : Finset ℝ) (w : ℝ → ℝ)
    (hsupport : ∀ x, x ∉ S → w x = 0)
    (hmom : ∀ m : ℕ, ∑ x ∈ S, w x * x ^ m = 0) :
    w = 0 := by
  funext x
  by_cases hx : x ∈ S
  · let p : ℝ[X] := ∏ y ∈ S.erase x, (Polynomial.X - Polynomial.C y)
    have hp_other : ∀ y ∈ S, y ≠ x → p.eval y = 0 := by
      intro y hy hyx
      have hyerase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨hyx, hy⟩
      simp only [p, Polynomial.eval_prod, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      exact Finset.prod_eq_zero hyerase (by simp)
    have hp_self : p.eval x ≠ 0 := by
      simp only [p, Polynomial.eval_prod, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      apply Finset.prod_ne_zero_iff.mpr
      intro y hy
      have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
      exact sub_ne_zero.mpr (Ne.symm hyne)
    have hpoly := polynomial_sum_eq_zero_of_moments S w hmom p
    rw [Finset.sum_eq_single x] at hpoly
    · exact (mul_eq_zero.mp hpoly).resolve_right hp_self
    · intro y hy hyx
      rw [hp_other y hy hyx]
      ring
    · simp [hx]
  · simpa using hsupport x hx

/-- Two finite atomic mass functions with the same moments are equal. -/
theorem atomicMass_ext_moments (μ ν : AtomicMass)
    (h : ∀ m : ℕ, atomicMoment μ m = atomicMoment ν m) : μ = ν := by
  let S := μ.support ∪ ν.support
  let w : ℝ → ℝ := fun x => μ x - ν x
  have hsupport : ∀ x, x ∉ S → w x = 0 := by
    intro x hx
    have hμ : x ∉ μ.support := fun hmem => hx (Finset.mem_union_left _ hmem)
    have hν : x ∉ ν.support := fun hmem => hx (Finset.mem_union_right _ hmem)
    simp [w, Finsupp.notMem_support_iff.mp hμ,
      Finsupp.notMem_support_iff.mp hν]
  have hmom : ∀ m : ℕ, ∑ x ∈ S, w x * x ^ m = 0 := by
    intro m
    have hμS : ∑ x ∈ S, μ x * x ^ m = atomicMoment μ m := by
      rw [atomicMoment, Finsupp.sum]
      symm
      apply Finset.sum_subset (Finset.subset_union_left)
      intro x _hxS hxμ
      rw [Finsupp.notMem_support_iff.mp hxμ]
      simp
    have hνS : ∑ x ∈ S, ν x * x ^ m = atomicMoment ν m := by
      rw [atomicMoment, Finsupp.sum]
      symm
      apply Finset.sum_subset (Finset.subset_union_right)
      intro x _hxS hxν
      rw [Finsupp.notMem_support_iff.mp hxν]
      simp
    simp only [w, sub_mul, Finset.sum_sub_distrib]
    rw [hμS, hνS, h m, sub_self]
  have hw := finite_support_eq_zero_of_moments S w hsupport hmom
  ext x
  have hx := congrFun hw x
  change μ x - ν x = 0 at hx
  linarith

end FinitePrecisionLanczos
