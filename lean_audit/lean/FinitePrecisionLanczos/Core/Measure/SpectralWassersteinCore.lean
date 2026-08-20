import FinitePrecisionLanczos.Core.Measure.Wasserstein
import Mathlib.Analysis.InnerProductSpace.PiL2









namespace FinitePrecisionLanczos

open scoped InnerProductSpace RealInnerProductSpace

variable {I : Type*} [Fintype I] [DecidableEq I]



lemma spectralSum_sub_eq_crossSum
    (u v : OrthonormalBasis I ℝ (EuclideanSpace ℝ I))
    (q : EuclideanSpace ℝ I) (lambda mu : I → ℝ) (f : ℝ → ℝ) :
    (∑ i, ⟪u i, q⟫_ℝ ^ 2 * f (lambda i)) -
        (∑ j, ⟪v j, q⟫_ℝ ^ 2 * f (mu j)) =
      ∑ i, ∑ j, ⟪u i, q⟫_ℝ * ⟪v j, q⟫_ℝ * ⟪u i, v j⟫_ℝ *
        (f (lambda i) - f (mu j)) := by
  have hu : ∀ i, ∑ j, ⟪u i, v j⟫_ℝ * ⟪v j, q⟫_ℝ = ⟪u i, q⟫_ℝ := by
    intro i
    exact v.sum_inner_mul_inner (u i) q
  have hv : ∀ j, ∑ i, ⟪u i, q⟫_ℝ * ⟪u i, v j⟫_ℝ = ⟪v j, q⟫_ℝ := by
    intro j
    simpa [real_inner_comm, mul_comm] using u.sum_inner_mul_inner (v j) q
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j =>
    ⟪u i, q⟫_ℝ * ⟪v j, q⟫_ℝ * ⟪u i, v j⟫_ℝ * f (mu j))]
  apply congrArg₂ (· - ·)
  · apply Fintype.sum_congr
    intro i
    calc
      ⟪u i, q⟫_ℝ ^ 2 * f (lambda i) =
          ⟪u i, q⟫_ℝ * (∑ j, ⟪u i, v j⟫_ℝ * ⟪v j, q⟫_ℝ) *
            f (lambda i) := by rw [hu i]; ring
      _ = ∑ j, ⟪u i, q⟫_ℝ * ⟪v j, q⟫_ℝ * ⟪u i, v j⟫_ℝ *
            f (lambda i) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Fintype.sum_congr
        intro j
        ring
  · apply Fintype.sum_congr
    intro j
    calc
      ⟪v j, q⟫_ℝ ^ 2 * f (mu j) =
          ⟪v j, q⟫_ℝ * (∑ i, ⟪u i, q⟫_ℝ * ⟪u i, v j⟫_ℝ) *
            f (mu j) := by rw [hv j]; ring
      _ = ∑ i, ⟪u i, q⟫_ℝ * ⟪v j, q⟫_ℝ * ⟪u i, v j⟫_ℝ *
            f (mu j) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Fintype.sum_congr
        intro i
        ring




theorem spectralSum_lipschitz_sub_le
    (u v : OrthonormalBasis I ℝ (EuclideanSpace ℝ I))
    (q : EuclideanSpace ℝ I) (hq : ‖q‖ = 1)
    (lambda mu : I → ℝ) (f : ℝ → ℝ) (hf : OneLipschitz f)
    (D : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (hcross : ∀ i j,
      (lambda i - mu j) * ⟪u i, v j⟫_ℝ = ⟪u i, D (v j)⟫_ℝ) :
    |(∑ i, ⟪u i, q⟫_ℝ ^ 2 * f (lambda i)) -
        (∑ j, ⟪v j, q⟫_ℝ ^ 2 * f (mu j))| ≤
      Real.sqrt (Fintype.card I) * ‖D‖ := by
  let a : I → ℝ := fun i => ⟪u i, q⟫_ℝ
  let b : I → ℝ := fun j => ⟪v j, q⟫_ℝ
  let e : I × I → ℝ := fun ij => ⟪u ij.1, D (v ij.2)⟫_ℝ
  let s : Finset (I × I) := Finset.univ
  have hexpand := spectralSum_sub_eq_crossSum u v q lambda mu f
  have hterm : ∀ i j,
      |⟪u i, q⟫_ℝ * ⟪v j, q⟫_ℝ * ⟪u i, v j⟫_ℝ *
          (f (lambda i) - f (mu j))| ≤
        |a i * b j| * |e (i, j)| := by
    intro i j
    have hlip := hf (lambda i) (mu j)
    have hc : |⟪u i, v j⟫_ℝ * (f (lambda i) - f (mu j))| ≤
        |e (i, j)| := by
      calc
        |⟪u i, v j⟫_ℝ * (f (lambda i) - f (mu j))| =
            |⟪u i, v j⟫_ℝ| * |f (lambda i) - f (mu j)| := abs_mul _ _
        _ ≤ |⟪u i, v j⟫_ℝ| * |lambda i - mu j| :=
          mul_le_mul_of_nonneg_left hlip (abs_nonneg _)
        _ = |e (i, j)| := by
          rw [← abs_mul, mul_comm, hcross]
    simpa [a, b, e, abs_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left hc (abs_nonneg (a i * b j))
  have habs :
      |∑ i, ∑ j, ⟪u i, q⟫_ℝ * ⟪v j, q⟫_ℝ * ⟪u i, v j⟫_ℝ *
          (f (lambda i) - f (mu j))| ≤
        ∑ ij ∈ s, |a ij.1 * b ij.2| * |e ij| := by
    calc
      |∑ i, ∑ j, ⟪u i, q⟫_ℝ * ⟪v j, q⟫_ℝ * ⟪u i, v j⟫_ℝ *
          (f (lambda i) - f (mu j))| ≤
          ∑ i, ∑ j, |⟪u i, q⟫_ℝ * ⟪v j, q⟫_ℝ * ⟪u i, v j⟫_ℝ *
            (f (lambda i) - f (mu j))| := abs_double_sum_le_sum_abs _
      _ ≤ ∑ i, ∑ j, |a i * b j| * |e (i, j)| := by
        apply Finset.sum_le_sum
        intro i _hi
        apply Finset.sum_le_sum
        intro j _hj
        exact hterm i j
      _ = ∑ ij ∈ s, |a ij.1 * b ij.2| * |e ij| := by
        symm
        simp only [s, Finset.mem_univ, ↓reduceIte]
        rw [Fintype.sum_prod_type]
  have hfirst : ∑ ij ∈ s, |a ij.1 * b ij.2| ^ 2 = 1 := by
    simp_rw [sq_abs, mul_pow]
    rw [show (∑ ij ∈ s, a ij.1 ^ 2 * b ij.2 ^ 2) =
        (∑ i, a i ^ 2) * (∑ j, b j ^ 2) by
      simp only [s, Finset.mem_univ, ↓reduceIte]
      rw [Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum (fun i => a i ^ 2) (fun j => b j ^ 2)).symm]
    rw [show ∑ i, a i ^ 2 = ‖q‖ ^ 2 by
      simpa [a] using u.sum_sq_inner_right q]
    rw [show ∑ j, b j ^ 2 = ‖q‖ ^ 2 by
      simpa [b] using v.sum_sq_inner_right q]
    simp [hq]
  have hsecond : ∑ ij ∈ s, |e ij| ^ 2 ≤ Fintype.card I * ‖D‖ ^ 2 := by
    rw [show (∑ ij ∈ s, |e ij| ^ 2) =
        ∑ j, ∑ i, |⟪u i, D (v j)⟫_ℝ| ^ 2 by
      simp only [s, Finset.mem_univ, ↓reduceIte]
      rw [Fintype.sum_prod_type, Finset.sum_comm]]
    calc
      ∑ j, ∑ i, |⟪u i, D (v j)⟫_ℝ| ^ 2 =
          ∑ j, ‖D (v j)‖ ^ 2 := by
        apply Fintype.sum_congr
        intro j
        simpa [sq_abs] using u.sum_sq_inner_right (D (v j))
      _ ≤ ∑ _j : I, ‖D‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _hj
        have hDj : ‖D (v j)‖ ≤ ‖D‖ := by
          simpa using D.le_opNorm (v j)
        exact pow_le_pow_left₀ (norm_nonneg _) hDj 2
      _ = Fintype.card I * ‖D‖ ^ 2 := by simp
  rw [hexpand]
  calc
    |∑ i, ∑ j, ⟪u i, q⟫_ℝ * ⟪v j, q⟫_ℝ * ⟪u i, v j⟫_ℝ *
        (f (lambda i) - f (mu j))| ≤
        ∑ ij ∈ s, |a ij.1 * b ij.2| * |e ij| := habs
    _ ≤ Real.sqrt (∑ ij ∈ s, |a ij.1 * b ij.2| ^ 2) *
        Real.sqrt (∑ ij ∈ s, |e ij| ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s _ _
    _ = Real.sqrt (∑ ij ∈ s, |e ij| ^ 2) := by rw [hfirst]; simp
    _ ≤ Real.sqrt (Fintype.card I * ‖D‖ ^ 2) :=
      Real.sqrt_le_sqrt hsecond
    _ = Real.sqrt (Fintype.card I) * ‖D‖ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg (Fintype.card I)), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (norm_nonneg D)]

end FinitePrecisionLanczos
