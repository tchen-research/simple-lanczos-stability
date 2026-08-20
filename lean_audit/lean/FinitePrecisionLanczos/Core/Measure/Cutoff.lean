import FinitePrecisionLanczos.Core.Measure.Wasserstein
import Mathlib.Topology.MetricSpace.Lipschitz










namespace FinitePrecisionLanczos

open Set


noncomputable def indexedAtomicMass {I : Type*} [Fintype I]
    (weight : I → ℝ) (x : I → ℝ) : AtomicMass :=
  ∑ i : I, Finsupp.single (x i) (weight i)


lemma atomicIntegral_indexedAtomicMass
    {I : Type*} [Fintype I]
    (weight : I → ℝ) (x : I → ℝ) (f : ℝ → ℝ) :
    atomicIntegral (indexedAtomicMass weight x) f =
      ∑ i : I, weight i * f (x i) := by
  classical
  unfold indexedAtomicMass
  let a : I → AtomicMass := fun i => Finsupp.single (x i) (weight i)
  let b : I → ℝ := fun i => weight i * f (x i)
  change atomicIntegral (∑ i : I, a i) f = ∑ i : I, b i
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih, a, b]



lemma exists_oneLipschitz_cutoff
    (S P : Set ℝ) [DecidablePred (fun z => z ∈ P)]
    (r : ℝ) (hr : 0 ≤ r)
    (hsep : ∀ z ∈ S, ∀ w ∈ S,
      (z ∈ P ∧ w ∉ P) ∨ (z ∉ P ∧ w ∈ P) → r ≤ |z - w|) :
    ∃ f : ℝ → ℝ, OneLipschitz f ∧
      ∀ z ∈ S, f z = if z ∈ P then r else 0 := by
  classical
  let label : ℝ → ℝ := fun z => if z ∈ P then r else 0
  have hlabel : LipschitzOnWith 1 label S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    by_cases hzP : z ∈ P <;> by_cases hwP : w ∈ P
    · simp [label, hzP, hwP]
    · have h := hsep z hz w hw (Or.inl ⟨hzP, hwP⟩)
      simpa [label, hzP, hwP, Real.dist_eq, abs_of_nonneg hr] using h
    · have h := hsep z hz w hw (Or.inr ⟨hzP, hwP⟩)
      simpa [label, hzP, hwP, Real.dist_eq, abs_of_nonneg hr,
        abs_sub_comm] using h
    · simp [label, hzP, hwP]
  obtain ⟨f, hf, heq⟩ := hlabel.extend_real
  refine ⟨f, ?_, ?_⟩
  · intro z w
    simpa [Real.dist_eq] using hf.dist_le_mul z w
  · intro z hz
    exact (heq hz).symm








theorem finiteGroupMass_cutoff_bound
    {I J : Type*} [Fintype I] [Fintype J]
    (source : I → ℝ) (target : J → ℝ)
    (x : I → ℝ) (y : J → ℝ)
    (G C : ℝ → Prop) [DecidablePred G] [DecidablePred C]
    (S P : Set ℝ)
    (hxS : ∀ i, x i ∈ S) (hyS : ∀ j, y j ∈ S)
    (hxP : ∀ i, x i ∈ P ↔ G (x i))
    (hyP : ∀ j, y j ∈ P ↔ C (y j))
    (r W : ℝ) (hr : 0 ≤ r)
    (hsep : ∀ z ∈ S, ∀ w ∈ S,
      (z ∈ P ∧ w ∉ P) ∨ (z ∉ P ∧ w ∈ P) → r ≤ |z - w|)
    (htest : ∀ f : ℝ → ℝ, OneLipschitz f →
      |atomicIntegral (indexedAtomicMass source x) f -
        atomicIntegral (indexedAtomicMass target y) f| ≤ W) :
    r * |finiteGroupMass source x G - finiteGroupMass target y C| ≤ W := by
  classical
  obtain ⟨f, hf, hfS⟩ := exists_oneLipschitz_cutoff S P r hr hsep
  have hfx : ∀ i, f (x i) = if G (x i) then r else 0 := by
    intro i
    rw [hfS (x i) (hxS i)]
    by_cases hG : G (x i)
    · have hP := (hxP i).mpr hG
      simp [hG, hP]
    · have hP : x i ∉ P := fun h => hG ((hxP i).mp h)
      simp [hG, hP]
  have hfy : ∀ j, f (y j) = if C (y j) then r else 0 := by
    intro j
    rw [hfS (y j) (hyS j)]
    by_cases hC : C (y j)
    · have hP := (hyP j).mpr hC
      simp [hC, hP]
    · have hP : y j ∉ P := fun h => hC ((hyP j).mp h)
      simp [hC, hP]
  have hid :
      atomicIntegral (indexedAtomicMass source x) f -
          atomicIntegral (indexedAtomicMass target y) f =
        r * (finiteGroupMass source x G - finiteGroupMass target y C) := by
    rw [atomicIntegral_indexedAtomicMass, atomicIntegral_indexedAtomicMass]
    unfold finiteGroupMass
    simp_rw [hfx, hfy]
    rw [mul_sub]
    simp_rw [Finset.mul_sum]
    apply congrArg₂ (· - ·)
    · apply Fintype.sum_congr
      intro i
      by_cases hG : G (x i) <;> simp [hG] <;> ring
    · apply Fintype.sum_congr
      intro j
      by_cases hC : C (y j) <;> simp [hC] <;> ring
  have h := htest f hf
  rw [hid, abs_mul, abs_of_nonneg hr] at h
  exact h

end FinitePrecisionLanczos
