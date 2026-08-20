import FinitePrecisionLanczos.Lanczos.Greenbaum.Completion

/-!
# Spectral consequences of the Greenbaum model

This optional extension proves a support
bound is proved directly from residuals, avoiding a black-box invocation of
Weyl's theorem.  In particular, the proof visibly reduces the physical
block operator `I_k \otimes H` to `k` copies of the residual theorem already
used in the Paige analysis.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- Squared Euclidean norm of a vector on a product index is the sum of the
squared norms of its physical blocks. -/
lemma coordNorm_prod_sq {n k : ℕ} (z : Fin k × Fin n → ℝ) :
    coordNorm z ^ 2 = ∑ r : Fin k, vnorm (fun i => z (r, i)) ^ 2 := by
  rw [coordNorm_sq]
  simp only [dotProduct, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _hr
  simpa [vdot, dotProduct] using (vnorm_sq (fun i => z (r, i))).symm

/-- A block diagonal matrix acts on each physical block separately. -/
lemma blockDiagonal_mulVec_apply {n k : ℕ} (H : Mat n n)
    (z : Fin k × Fin n → ℝ) (r : Fin k) (i : Fin n) :
    Matrix.mulVec (blockDiagonal H) z (r, i) =
      Matrix.mulVec H (fun j => z (r, j)) i := by
  simp [blockDiagonal, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

/-- Residual distance-to-spectrum estimate for `I_k \otimes H`.

The distance is to the spectrum of the original `H`, not to a separately
defined spectrum of the block matrix.  This is the exact multiplicity
reduction used below. -/
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

/-- A matrix with orthonormal columns preserves Euclidean vector norms. -/
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

/-- Real transpose symmetry implies Hermitian symmetry on any finite index
type. -/
lemma indexed_isHermitian_of_transpose_eq {I : Type*} [Fintype I]
    {A : Matrix I I ℝ} (hA : Matrix.transpose A = A) : A.IsHermitian := by
  show Matrix.conjTranspose A = A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hA

/-- Eigenvalue support localization for any completed Greenbaum model.

The canonical eigenvalue enumeration covers every eigenvalue of the
symmetric model matrix. -/
theorem greenbaum_model_eigenvalue_localization {n k : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : 0 < n) (H : Mat n n) (hH : Matrix.transpose H = H)
    (U : Matrix (Fin k × Fin n) ι ℝ)
    (hUtU : Matrix.transpose U * U = 1)
    (hUUt : U * Matrix.transpose U = 1)
    (T : Matrix ι ι ℝ) (hT : Matrix.transpose T = T) (i : ι) :
    spectralDistance H
        ((indexed_isHermitian_of_transpose_eq hT).eigenvalues i) ≤
      ‖Matrix.transpose U * blockDiagonal H * U - T‖ := by
  let hTherm : T.IsHermitian := indexed_isHermitian_of_transpose_eq hT
  let theta := hTherm.eigenvalues i
  let y : ι → ℝ := ⇑(hTherm.eigenvectorBasis i)
  let z : Fin k × Fin n → ℝ := Matrix.mulVec U y
  let S : Matrix ι ι ℝ := Matrix.transpose U * blockDiagonal H * U
  have hyunit : coordNorm y = 1 := by
    change ‖hTherm.eigenvectorBasis i‖ = 1
    exact hTherm.eigenvectorBasis.orthonormal.1 i
  have hzunit : coordNorm z = 1 := by
    rw [show z = Matrix.mulVec U y from rfl,
      coordNorm_mulVec_eq_of_gram U hUtU,
      hyunit]
  have heig : Matrix.mulVec T y = theta • y := by
    exact hTherm.mulVec_eigenvectorBasis i
  have hAU : blockDiagonal H * U = U * S := by
    calc
      blockDiagonal H * U = 1 * blockDiagonal H * U := by rw [Matrix.one_mul]
      _ = (U * Matrix.transpose U) * blockDiagonal H * U := by rw [hUUt]
      _ = U * S := by simp [S, Matrix.mul_assoc]
  have hresidual :
      Matrix.mulVec (blockDiagonal H) z - theta • z =
        Matrix.mulVec U (Matrix.mulVec (S - T) y) := by
    rw [show z = Matrix.mulVec U y from rfl, Matrix.mulVec_mulVec, hAU,
      ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, heig]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hresidual_bound :
      coordNorm (Matrix.mulVec (blockDiagonal H) z - theta • z) ≤ ‖S - T‖ := by
    rw [hresidual, coordNorm_mulVec_eq_of_gram U hUtU]
    calc
      coordNorm (Matrix.mulVec (S - T) y) ≤ ‖S - T‖ * coordNorm y :=
        coordNorm_mulVec_le (S - T) y
      _ = ‖S - T‖ := by rw [hyunit, mul_one]
  have hdist := spectralDistance_mul_coordNorm_le_blockResidual
    hn H hH theta z
  rw [hzunit, mul_one] at hdist
  exact hdist.trans (by simpa [S] using hresidual_bound)

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- Instantiation of support localization for every completion produced above. -/
theorem completed_eigenvalue_localization
    {d : ℕ} (U : Matrix (Fin k × Fin n) (Fin k ⊕ Fin d) ℝ)
    (hUtU : Matrix.transpose U * U = 1)
    (hUUt : U * Matrix.transpose U = 1)
    (Ttilde : Matrix (Fin k ⊕ Fin d) (Fin k ⊕ Fin d) ℝ)
    (hT : Matrix.transpose Ttilde = Ttilde) (i : Fin k ⊕ Fin d) :
    spectralDistance L.H
        ((indexed_isHermitian_of_transpose_eq hT).eigenvalues i) ≤
      ‖Matrix.transpose U * L.greenbaumBlockOperator * U - Ttilde‖ := by
  simpa [greenbaumBlockOperator] using
    greenbaum_model_eigenvalue_localization L.ambient_pos L.H L.hHsymm
      U hUtU hUUt Ttilde hT i

end LanczosRun
end FinitePrecisionLanczos
