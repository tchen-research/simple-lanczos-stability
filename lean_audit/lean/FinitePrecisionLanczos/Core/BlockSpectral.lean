import FinitePrecisionLanczos.Core.Spectral
import FinitePrecisionLanczos.Core.DilationRecurrence


namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

lemma coordNorm_prod_sq {n k : ℕ} (z : Fin k × Fin n → ℝ) :
    coordNorm z ^ 2 = ∑ r : Fin k, vnorm (fun i => z (r, i)) ^ 2 := by
  rw [coordNorm_sq]
  simp only [dotProduct, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _hr
  simpa [vdot, dotProduct] using (vnorm_sq (fun i => z (r, i))).symm

lemma blockDiagonal_mulVec_apply {n k : ℕ} (H : Mat n n)
    (z : Fin k × Fin n → ℝ) (r : Fin k) (i : Fin n) :
    Matrix.mulVec (blockDiagonal H) z (r, i) =
      Matrix.mulVec H (fun j => z (r, j)) i := by
  simp [blockDiagonal, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem spectralDistance_mul_coordNorm_le_blockResidual {n k : ℕ}
    (hn : 0 < n) (H : Mat n n) (hH : Matrix.transpose H = H)
    (theta : ℝ) (z : Fin k × Fin n → ℝ) :
    spectralDistance H theta * coordNorm z ≤
      coordNorm (Matrix.mulVec (blockDiagonal H) z - theta • z) := by
  let R : Fin k × Fin n → ℝ :=
    Matrix.mulVec (blockDiagonal H) z - theta • z
  have hslice : ∀ r : Fin k,
      (fun i => R (r, i)) =
        Matrix.mulVec H (fun i => z (r, i)) -
          theta • (fun i => z (r, i)) := by
    intro r
    funext i
    simp only [R, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [blockDiagonal_mulVec_apply]
  let d := spectralDistance H theta
  have hd : 0 ≤ d :=
    spectralDistance_nonneg hn (isHermitian_of_transpose_eq hH) theta
  have hblock : ∀ r : Fin k,
      d * vnorm (fun i => z (r, i)) ≤ vnorm (fun i => R (r, i)) := by
    intro r
    rw [hslice r]
    exact spectralDistance_mul_vnorm_le_residual hn hH theta
      (fun i => z (r, i))
  have hblock_sq : ∀ r : Fin k,
      d ^ 2 * vnorm (fun i => z (r, i)) ^ 2 ≤
        vnorm (fun i => R (r, i)) ^ 2 := by
    intro r
    have hleft := vnorm_nonneg (fun i => z (r, i))
    have hright := vnorm_nonneg (fun i => R (r, i))
    calc
      d ^ 2 * vnorm (fun i => z (r, i)) ^ 2 =
          (d * vnorm (fun i => z (r, i))) ^ 2 := by ring
      _ ≤ vnorm (fun i => R (r, i)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hd hleft) (hblock r) 2
  have hsum := Finset.sum_le_sum fun r (_hr : r ∈ Finset.univ) => hblock_sq r
  have hsq : d ^ 2 * coordNorm z ^ 2 ≤ coordNorm R ^ 2 := by
    rw [coordNorm_prod_sq, coordNorm_prod_sq]
    rw [Finset.mul_sum]
    exact hsum
  have hz := coordNorm_nonneg z
  have hR := coordNorm_nonneg R
  change d * coordNorm z ≤ coordNorm R
  rw [← sq_le_sq₀ (mul_nonneg hd hz) hR]
  simpa [mul_pow] using hsq

theorem coordNorm_mulVec_eq_of_gram {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (U : Matrix I J ℝ) (hU : Matrix.transpose U * U = 1) (x : J → ℝ) :
    coordNorm (Matrix.mulVec U x) = coordNorm x := by
  have hsq : coordNorm (Matrix.mulVec U x) ^ 2 = coordNorm x ^ 2 := by
    rw [coordNorm_sq, coordNorm_sq]
    calc
      Matrix.mulVec U x ⬝ᵥ Matrix.mulVec U x =
          x ⬝ᵥ Matrix.mulVec (Matrix.transpose U) (Matrix.mulVec U x) := by
        symm
        exact Matrix.dotProduct_transpose_mulVec U x (Matrix.mulVec U x)
      _ = x ⬝ᵥ Matrix.mulVec (Matrix.transpose U * U) x := by
        rw [Matrix.mulVec_mulVec]
      _ = x ⬝ᵥ x := by rw [hU, Matrix.one_mulVec]
  nlinarith [coordNorm_nonneg (Matrix.mulVec U x), coordNorm_nonneg x]

lemma indexed_isHermitian_of_transpose_eq {I : Type*} [Fintype I]
    {A : Matrix I I ℝ} (hA : Matrix.transpose A = A) : A.IsHermitian := by
  show Matrix.conjTranspose A = A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hA


section CoordNorm

variable {ι : Type*} [Fintype ι]

lemma coordNorm_add_le (x y : ι → ℝ) :
    coordNorm (x + y) ≤ coordNorm x + coordNorm y := by
  simpa [coordNorm] using
    norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (WithLp.toLp 2 y)

lemma coordNorm_smul (c : ℝ) (x : ι → ℝ) :
    coordNorm (c • x) = |c| * coordNorm x := by
  simp [coordNorm, norm_smul]

lemma abs_dotProduct_le_coordNorm (x y : ι → ℝ) :
    |x ⬝ᵥ y| ≤ coordNorm x * coordNorm y := by
  have hinner :
      inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (WithLp.toLp 2 y) =
        x ⬝ᵥ y := by
    calc
      inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (WithLp.toLp 2 y) =
          y ⬝ᵥ x := by
        simpa [star_trivial] using EuclideanSpace.inner_toLp_toLp x y
      _ = x ⬝ᵥ y := dotProduct_comm _ _
  rw [← hinner, coordNorm, coordNorm]
  exact abs_real_inner_le_norm _ _

lemma abs_dotProduct_mulVec_le [DecidableEq ι] (A : Matrix ι ι ℝ)
    (x : ι → ℝ) :
    |x ⬝ᵥ (A *ᵥ x)| ≤ ‖A‖ * coordNorm x ^ 2 := by
  calc
    |x ⬝ᵥ (A *ᵥ x)| ≤ coordNorm x * coordNorm (A *ᵥ x) :=
      abs_dotProduct_le_coordNorm _ _
    _ ≤ coordNorm x * (‖A‖ * coordNorm x) :=
      mul_le_mul_of_nonneg_left (coordNorm_mulVec_le A x) (coordNorm_nonneg _)
    _ = ‖A‖ * coordNorm x ^ 2 := by ring

end CoordNorm


section Block

variable {n k : ℕ}

lemma dotProduct_blockDiagonal_mulVec (H : Mat n n)
    (z : Fin k × Fin n → ℝ) :
    z ⬝ᵥ (blockDiagonal H *ᵥ z) =
      ∑ r : Fin k, vdot (fun i => z (r, i)) (H *ᵥ fun i => z (r, i)) := by
  simp only [dotProduct, Fintype.sum_prod_type, vdot]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  rw [blockDiagonal_mulVec_apply]

lemma dotProduct_self_prod (z : Fin k × Fin n → ℝ) :
    z ⬝ᵥ z = ∑ r : Fin k, vdot (fun i => z (r, i)) (fun i => z (r, i)) := by
  simp [dotProduct, Fintype.sum_prod_type, vdot]

theorem dotProduct_blockDiagonal_le_spectralMax (hn : 0 < n) {H : Mat n n}
    (hH : Hᵀ = H) (z : Fin k × Fin n → ℝ) :
    z ⬝ᵥ (blockDiagonal H *ᵥ z) ≤ spectralMax H * (z ⬝ᵥ z) := by
  rw [dotProduct_blockDiagonal_mulVec, dotProduct_self_prod, Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ =>
    vdot_mulVec_le_spectralMax hn hH (fun i => z (r, i))

theorem spectralMin_le_dotProduct_blockDiagonal (hn : 0 < n) {H : Mat n n}
    (hH : Hᵀ = H) (z : Fin k × Fin n → ℝ) :
    spectralMin H * (z ⬝ᵥ z) ≤ z ⬝ᵥ (blockDiagonal H *ᵥ z) := by
  rw [dotProduct_blockDiagonal_mulVec, dotProduct_self_prod, Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ =>
    spectralMin_mul_vdot_le hn hH (fun i => z (r, i))

end Block

end FinitePrecisionLanczos
