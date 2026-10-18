import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic


open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace FinitePrecisionLanczos

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

abbrev Vec (n : ℕ) := Fin n → ℝ

noncomputable def vnorm {n : ℕ} (x : Vec n) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖

noncomputable def coordNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖

def vdot {n : ℕ} (x y : Vec n) : ℝ := x ⬝ᵥ y

variable {l m n p : ℕ}

lemma isHermitian_of_transpose_eq {A : Mat n n} (hA : Aᵀ = A) : A.IsHermitian := by
  show Aᴴ = A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hA

@[simp] lemma vnorm_zero : vnorm (0 : Vec n) = 0 := by
  simp [vnorm]

lemma vnorm_nonneg (x : Vec n) : 0 ≤ vnorm x := norm_nonneg _

lemma vnorm_smul (a : ℝ) (x : Vec n) : vnorm (a • x) = |a| * vnorm x := by
  simp [vnorm, norm_smul]

@[simp] lemma vnorm_neg (x : Vec n) : vnorm (-x) = vnorm x := by
  simp [vnorm]

lemma vnorm_add_le (x y : Vec n) : vnorm (x + y) ≤ vnorm x + vnorm y := by
  exact norm_add_le _ _

lemma vnorm_sub_le (x y : Vec n) : vnorm (x - y) ≤ vnorm x + vnorm y := by
  simpa [vnorm] using norm_sub_le
    (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y)

lemma vnorm_sq (x : Vec n) : vnorm x ^ 2 = vdot x x := by
  rw [vnorm, ← real_inner_self_eq_norm_sq]
  simpa [vdot, star_trivial] using
    (EuclideanSpace.inner_toLp_toLp x x :
      ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)), WithLp.toLp 2 x⟫_ℝ = _)

lemma coordNorm_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    coordNorm x ^ 2 = x ⬝ᵥ x := by
  rw [coordNorm, ← real_inner_self_eq_norm_sq]
  simpa [star_trivial] using
    (EuclideanSpace.inner_toLp_toLp x x :
      ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ ι), WithLp.toLp 2 x⟫_ℝ = _)

lemma coordNorm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ coordNorm x := norm_nonneg _

lemma abs_vdot_le (x y : Vec n) : |vdot x y| ≤ vnorm x * vnorm y := by
  have hinner :
      ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)), WithLp.toLp 2 y⟫_ℝ = x ⬝ᵥ y := by
    calc
      ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)), WithLp.toLp 2 y⟫_ℝ
          = y ⬝ᵥ x := by simpa [star_trivial] using EuclideanSpace.inner_toLp_toLp x y
      _ = x ⬝ᵥ y := dotProduct_comm _ _
  rw [vdot, ← hinner, vnorm, vnorm]
  exact abs_real_inner_le_norm _ _

lemma vnorm_mulVec_le (A : Mat m n) (x : Vec n) :
    vnorm (A *ᵥ x) ≤ ‖A‖ * vnorm x := by
  simpa [vnorm] using
    A.l2_opNorm_mulVec (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))

lemma coordNorm_mulVec_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ ℝ) (x : κ → ℝ) :
    coordNorm (A *ᵥ x) ≤ ‖A‖ * coordNorm x := by
  simpa [coordNorm] using
    A.l2_opNorm_mulVec (WithLp.toLp 2 x : EuclideanSpace ℝ κ)

lemma norm_mul_le (A : Mat m n) (B : Mat n p) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  Matrix.l2_opNorm_mul A B

lemma norm_transpose (A : Mat m n) : ‖Aᵀ‖ = ‖A‖ := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial A]
  exact Matrix.l2_opNorm_conjTranspose A

def ofCols (q : Fin k → Vec n) : Mat n k := fun i j => q j i

@[simp] lemma ofCols_apply (q : Fin k → Vec n) (i : Fin n) (j : Fin k) :
    ofCols q i j = q j i := rfl

noncomputable def matCLM (A : Mat m n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ)).trans LinearMap.toContinuousLinearMap) A

noncomputable def indexedMatCLM {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ ℝ) :
    EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ)).trans LinearMap.toContinuousLinearMap) A

lemma norm_indexedMatCLM {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ ℝ) : ‖indexedMatCLM A‖ = ‖A‖ := rfl

lemma indexedMatCLM_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ ℝ) (x : EuclideanSpace ℝ κ) :
    indexedMatCLM A x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl

lemma norm_matCLM (A : Mat m n) : ‖matCLM A‖ = ‖A‖ := rfl

lemma matCLM_apply (A : Mat m n) (x : EuclideanSpace ℝ (Fin n)) :
    matCLM A x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl

theorem indexed_norm_le_one_of_gram {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (X : Matrix I J ℝ) (hX : Xᵀ * X = 1) : ‖X‖ ≤ 1 := by
  rw [← norm_indexedMatCLM]
  refine (indexedMatCLM X).opNorm_le_bound (by norm_num) fun x => ?_
  rw [indexedMatCLM_apply]
  change coordNorm (X *ᵥ WithLp.ofLp x) ≤ 1 * ‖x‖
  have hsq : coordNorm (X *ᵥ WithLp.ofLp x) ^ 2 =
      coordNorm (WithLp.ofLp x) ^ 2 := by
    rw [coordNorm_sq, coordNorm_sq]
    calc
      (X *ᵥ WithLp.ofLp x) ⬝ᵥ (X *ᵥ WithLp.ofLp x) =
          WithLp.ofLp x ⬝ᵥ Xᵀ *ᵥ (X *ᵥ WithLp.ofLp x) := by
        symm
        exact Matrix.dotProduct_transpose_mulVec X (WithLp.ofLp x)
          (X *ᵥ WithLp.ofLp x)
      _ = WithLp.ofLp x ⬝ᵥ ((Xᵀ * X) *ᵥ WithLp.ofLp x) := by
        rw [Matrix.mulVec_mulVec]
      _ = WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by rw [hX, Matrix.one_mulVec]
  have hleft := coordNorm_nonneg (X *ᵥ WithLp.ofLp x)
  have hright : coordNorm (WithLp.ofLp x) = ‖x‖ := rfl
  rw [one_mul, ← hright]
  have hnorm := norm_nonneg x
  nlinarith [sq_nonneg
    (coordNorm (X *ᵥ WithLp.ofLp x) + coordNorm (WithLp.ofLp x))]

lemma indexed_norm_transpose {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (X : Matrix I J ℝ) : ‖Xᵀ‖ = ‖X‖ := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial X]
  exact Matrix.l2_opNorm_conjTranspose X

lemma abs_apply_le_vnorm (x : Vec n) (j : Fin n) : |x j| ≤ vnorm x := by
  simpa [vnorm, Real.norm_eq_abs] using
    (PiLp.norm_apply_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) j)

lemma vnorm_sum_le {ι : Type*} [Fintype ι] (q : ι → Vec n) :
    vnorm (∑ i, q i) ≤ ∑ i, vnorm (q i) := by
  have hsum : (WithLp.toLp 2 (∑ i, q i) : EuclideanSpace ℝ (Fin n))
      = ∑ i, (WithLp.toLp 2 (q i) : EuclideanSpace ℝ (Fin n)) := by
    ext j
    simp
  simp only [vnorm, hsum]
  exact norm_sum_le _ _

lemma ofCols_mulVec (q : Fin k → Vec n) (x : Vec k) :
    ofCols q *ᵥ x = ∑ j, x j • q j := by
  ext i
  simp only [Matrix.mulVec, ofCols, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The columnwise Frobenius estimate used in the paper. -/
lemma norm_ofCols_le_sqrt_sum (q : Fin k → Vec n) :
    ‖ofCols q‖ ≤ Real.sqrt (∑ j, vnorm (q j) ^ 2) := by
  rw [← norm_matCLM]
  refine (matCLM (ofCols q)).opNorm_le_bound (Real.sqrt_nonneg _) fun x => ?_
  rw [matCLM_apply]
  change vnorm (ofCols q *ᵥ WithLp.ofLp x) ≤ _
  rw [ofCols_mulVec]
  have hx : (∑ j, |WithLp.ofLp x j| ^ 2) = ‖x‖ ^ 2 := by
    simpa [EuclideanSpace.norm_sq_eq, sq_abs]
  calc
    vnorm (∑ j, WithLp.ofLp x j • q j) ≤
        ∑ j, vnorm (WithLp.ofLp x j • q j) := vnorm_sum_le _
    _ = ∑ j, |WithLp.ofLp x j| * vnorm (q j) := by simp_rw [vnorm_smul]
    _ ≤ Real.sqrt (∑ j, |WithLp.ofLp x j| ^ 2) *
        Real.sqrt (∑ j, vnorm (q j) ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ j, vnorm (q j) ^ 2) * ‖x‖ := by
      rw [hx, Real.sqrt_sq (norm_nonneg x), mul_comm]

/-- In particular, k columns of norm at most B have operator norm at most √k B. -/
lemma norm_ofCols_le_sqrt_card (q : Fin k → Vec n) (B : ℝ) (hB : 0 ≤ B)
    (hq : ∀ j, vnorm (q j) ≤ B) :
    ‖ofCols q‖ ≤ Real.sqrt (k : ℝ) * B := by
  calc
    ‖ofCols q‖ ≤ Real.sqrt (∑ j, vnorm (q j) ^ 2) := norm_ofCols_le_sqrt_sum q
    _ ≤ Real.sqrt (∑ _j : Fin k, B ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (vnorm_nonneg _) (hq j) 2
    _ = Real.sqrt (k : ℝ) * B := by
      simp [Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_sq hB]

lemma norm_ofCols_le_sum (q : Fin k → Vec n) :
    ‖ofCols q‖ ≤ ∑ j, vnorm (q j) := by
  rw [← norm_matCLM]
  refine (matCLM (ofCols q)).opNorm_le_bound (Finset.sum_nonneg fun _ _ => vnorm_nonneg _)
    fun x => ?_
  rw [matCLM_apply]
  change vnorm (ofCols q *ᵥ WithLp.ofLp x) ≤ (∑ j, vnorm (q j)) * ‖x‖
  rw [ofCols_mulVec]
  calc
    vnorm (∑ j, WithLp.ofLp x j • q j)
        ≤ ∑ j, vnorm (WithLp.ofLp x j • q j) := vnorm_sum_le _
    _ = ∑ j, |WithLp.ofLp x j| * vnorm (q j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [vnorm_smul]
    _ ≤ ∑ j, ‖x‖ * vnorm (q j) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (by simpa [vnorm] using abs_apply_le_vnorm (WithLp.ofLp x) j)
        (vnorm_nonneg _)
    _ = (∑ j, vnorm (q j)) * ‖x‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma norm_le_of_abs_row_col_sum_le (A : Mat m n) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, ∑ j, |A i j| ≤ B) (hcol : ∀ j, ∑ i, |A i j| ≤ B) :
    ‖A‖ ≤ B := by
  rw [← norm_matCLM]
  refine (matCLM A).opNorm_le_bound hB fun x => ?_
  rw [matCLM_apply]
  change vnorm (A *ᵥ WithLp.ofLp x) ≤ B * ‖x‖
  have hx : ‖x‖ = vnorm (WithLp.ofLp x) := by simp [vnorm]
  rw [hx]
  set y : Vec n := WithLp.ofLp x
  have hrowsq : ∀ i, ((A *ᵥ y) i) ^ 2 ≤ B * ∑ j, |A i j| * y j ^ 2 := by
    intro i
    have h1 : |(A *ᵥ y) i| ≤ ∑ j, |A i j| * |y j| := by
      simp only [Matrix.mulVec, dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      simp [abs_mul]
    have h2 : (∑ j, |A i j| * |y j|) ^ 2
        ≤ (∑ j, |A i j|) * ∑ j, |A i j| * y j ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => abs_nonneg _)
        (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
        (fun j _ => le_of_eq (by rw [mul_pow, sq_abs, sq_abs, ← sq_abs (A i j)]; ring))
    have h3 : 0 ≤ ∑ j, |A i j| * y j ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
    calc
      ((A *ᵥ y) i) ^ 2 = |(A *ᵥ y) i| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ j, |A i j| * |y j|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ (∑ j, |A i j|) * ∑ j, |A i j| * y j ^ 2 := h2
      _ ≤ B * ∑ j, |A i j| * y j ^ 2 := mul_le_mul_of_nonneg_right (hrow i) h3
  have hsq : vnorm (A *ᵥ y) ^ 2 ≤ (B * vnorm y) ^ 2 := by
    rw [mul_pow, vnorm_sq, vnorm_sq]
    simp only [vdot, dotProduct]
    calc
      ∑ i, (A *ᵥ y) i * (A *ᵥ y) i = ∑ i, ((A *ᵥ y) i) ^ 2 := by
        simp only [sq]
      _ ≤ ∑ i, B * ∑ j, |A i j| * y j ^ 2 := Finset.sum_le_sum fun i _ => hrowsq i
      _ = B * ∑ j, (∑ i, |A i j|) * y j ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
      _ ≤ B * ∑ j, B * y j ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hB
        exact Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
      _ = B ^ 2 * ∑ j, y j * y j := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
  exact (pow_le_pow_iff_left₀ (vnorm_nonneg _) (mul_nonneg hB (vnorm_nonneg _))
    two_ne_zero).mp hsq

lemma norm_le_card_mul_of_entry_bound (A : Mat k k) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ i j, |A i j| ≤ B) : ‖A‖ ≤ (k : ℝ) * B := by
  have hsum : ∀ (f : Fin k → ℝ), (∀ j, |f j| ≤ B) → ∑ j, |f j| ≤ (k : ℝ) * B := by
    intro f hf
    calc
      ∑ j, |f j| ≤ ∑ _j : Fin k, B := Finset.sum_le_sum fun j _ => hf j
      _ = (k : ℝ) * B := by simp
  exact norm_le_of_abs_row_col_sum_le A _ (mul_nonneg (Nat.cast_nonneg k) hB)
    (fun i => hsum _ fun j => hA i j) (fun j => hsum _ fun i => hA i j)

lemma vnorm_eq_one_of_vdot_self (y : Vec n) (hy : vdot y y = 1) : vnorm y = 1 := by
  have hs := vnorm_sq y
  rw [hy] at hs
  nlinarith [vnorm_nonneg y]

lemma vnorm_col_le_opNorm (A : Mat m p) (j : Fin p) : vnorm (fun r => A r j) ≤ ‖A‖ := by
  have hcol : (fun r => A r j) = A *ᵥ Pi.single j 1 := by
    ext r
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have he : vnorm (Pi.single j (1 : ℝ) : Vec p) = 1 :=
    vnorm_eq_one_of_vdot_self _ (by simp [vdot])
  rw [hcol]
  calc
    vnorm (A *ᵥ Pi.single j 1) ≤ ‖A‖ * vnorm (Pi.single j (1 : ℝ) : Vec p) :=
      vnorm_mulVec_le _ _
    _ = ‖A‖ := by rw [he, mul_one]

lemma abs_quadratic_le_opNorm (M : Mat k k) (y : Vec k)
    (hy : vdot y y = 1) : |vdot y (M *ᵥ y)| ≤ ‖M‖ := by
  have hv := vnorm_eq_one_of_vdot_self y hy
  calc
    |vdot y (M *ᵥ y)| ≤ vnorm y * vnorm (M *ᵥ y) := abs_vdot_le _ _
    _ ≤ vnorm y * (‖M‖ * vnorm y) :=
      mul_le_mul_of_nonneg_left (vnorm_mulVec_le M y) (vnorm_nonneg _)
    _ = ‖M‖ := by rw [hv]; ring

end FinitePrecisionLanczos
