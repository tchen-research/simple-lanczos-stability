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

lemma vnorm_eq_zero {x : Vec n} : vnorm x = 0 ↔ x = 0 := by
  rw [vnorm, norm_eq_zero]
  exact WithLp.toLp_eq_zero 2

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


lemma vnorm_le_sum_abs (x : Vec n) : vnorm x ≤ ∑ i, |x i| := by
  have hx : x = ∑ i : Fin n, x i • Pi.single i 1 := by
    ext j
    classical
    simp [Pi.single_apply]
  calc
    vnorm x = vnorm (∑ i : Fin n, x i • Pi.single i 1) := congrArg vnorm hx
    _
        ≤ ∑ i : Fin n, vnorm (x i • Pi.single i 1) := vnorm_sum_le _
    _ = ∑ i : Fin n, |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [vnorm_smul]
      simp [vnorm]


lemma ofCols_mulVec (q : Fin k → Vec n) (x : Vec k) :
    ofCols q *ᵥ x = ∑ j, x j • q j := by
  ext i
  simp only [Matrix.mulVec, ofCols, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring



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



lemma norm_le_card_mul_card_mul_of_entry_bound (A : Mat m n) (B : ℝ)
    (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B) :
    ‖A‖ ≤ (m : ℝ) * (n : ℝ) * B := by
  calc
    ‖A‖ ≤ ∑ j : Fin n, vnorm (fun i => A i j) := norm_ofCols_le_sum _
    _ ≤ ∑ _j : Fin n, ∑ _i : Fin m, B := by
      apply Finset.sum_le_sum
      intro j _
      exact (vnorm_le_sum_abs (fun i => A i j)).trans
        (Finset.sum_le_sum fun i _ => hA i j)
    _ = (m : ℝ) * (n : ℝ) * B := by simp; ring

end FinitePrecisionLanczos
