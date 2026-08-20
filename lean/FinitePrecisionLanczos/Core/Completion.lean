import FinitePrecisionLanczos.Core.CompletionBasis

/-!
# Matrix form of the exact completion theorem

This file translates the basis-level continuation theorem back to the
coordinate matrices used in lem:completion and thm:greenbaum.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

variable {I J : Type*} [Fintype I] [Fintype J]

/-- A matrix column regarded as a vector in Euclidean space. -/
noncomputable def euclideanColumn (X : Matrix I J ℝ) (j : J) :
    EuclideanSpace ℝ I :=
  WithLp.toLp 2 (fun i => X i j)

lemma euclideanColumn_apply (X : Matrix I J ℝ) (j : J) (i : I) :
    euclideanColumn X j i = X i j := rfl

lemma inner_euclideanColumn (X : Matrix I J ℝ) (i j : J) :
    ⟪euclideanColumn X i, euclideanColumn X j⟫_ℝ =
      (Matrix.transpose X * X) i j := by
  classical
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro l _
  change X l j * X l i = X l i * X l j
  ring

theorem orthonormal_euclideanColumn [DecidableEq J]
    (X : Matrix I J ℝ) (hX : Matrix.transpose X * X = 1) :
    Orthonormal ℝ (euclideanColumn X) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_euclideanColumn, hX, Matrix.one_apply]

/-- A square matrix regarded as a linear operator on Euclidean space. -/
noncomputable def euclideanOperator [DecidableEq I] (A : Matrix I I ℝ) :
    EuclideanSpace ℝ I →ₗ[ℝ] EuclideanSpace ℝ I :=
  A.toEuclideanLin

lemma euclideanOperator_apply_column [DecidableEq I]
    (A : Matrix I I ℝ) (X : Matrix I J ℝ) (j : J) :
    euclideanOperator A (euclideanColumn X j) =
      euclideanColumn (A * X) j := by
  ext i
  simp [euclideanOperator, euclideanColumn, Matrix.mul_apply,
    Matrix.mulVec, dotProduct]

theorem euclideanOperator_isSymmetric [DecidableEq I]
    (A : Matrix I I ℝ) (hA : Matrix.transpose A = A) :
    (euclideanOperator A).IsSymmetric := by
  unfold euclideanOperator
  rw [Matrix.isSymmetric_toEuclideanLin_iff]
  show Matrix.conjTranspose A = A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hA

lemma euclideanColumn_smul (c : ℝ) (p : I → ℝ) :
    euclideanColumn (Matrix.of fun i (_ : Unit) => c * p i) () =
      c • (WithLp.toLp 2 p : EuclideanSpace ℝ I) := by
  ext i
  simp [euclideanColumn]

/-- Columnwise conversion of an exact matrix Lanczos recurrence to the
basis-level recurrence consumed by exact continuation. -/
theorem matrix_recurrence_to_columns {k : ℕ} (hk : 0 < k)
    [DecidableEq I]
    (A : Matrix I I ℝ) (X : Matrix I (Fin k) ℝ)
    (T : Matrix (Fin k) (Fin k) ℝ) (r : I → ℝ)
    (hrec : A * X = X * T + lastOuter hk r) :
    ∀ j, euclideanOperator A (euclideanColumn X j) =
      (∑ i, T i j • euclideanColumn X i) +
        if j = ⟨k - 1, by omega⟩ then
          (WithLp.toLp 2 r : EuclideanSpace ℝ I) else 0 := by
  classical
  intro j
  rw [euclideanOperator_apply_column]
  ext l
  simp only [euclideanColumn, WithLp.ofLp_toLp, WithLp.ofLp_add,
    WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero,
    Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.zero_apply,
    smul_eq_mul]
  have hcol := congrArg (fun M : Matrix I (Fin k) ℝ => M l j) hrec
  rw [hcol]
  simp only [Matrix.add_apply, Matrix.mul_apply, lastOuter,
    Matrix.vecMulVec, lastCoord]
  by_cases hj : j = ⟨k - 1, by omega⟩
  · subst j
    simp [Pi.single_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · have hjval : j.1 ≠ k - 1 := by
      intro h
      apply hj
      exact Fin.ext h
    simp [hj, Pi.single_apply, hjval]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Orthogonality of the matrix boundary vector to the computed columns. -/
theorem matrix_boundary_orthogonal {k : ℕ}
    (X : Matrix I (Fin k) ℝ) (r : I → ℝ)
    (hr : Matrix.mulVec (Matrix.transpose X) r = 0) :
    ∀ i, ⟪euclideanColumn X i,
      (WithLp.toLp 2 r : EuclideanSpace ℝ I)⟫_ℝ = 0 := by
  classical
  intro i
  have hi := congrArg (fun z : Fin k → ℝ => z i) hr
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply,
    Matrix.transpose_apply] at hi
  rw [EuclideanSpace.inner_toLp_toLp]
  change r ⬝ᵥ (fun l => X l i) = 0
  rw [dotProduct_comm]
  exact hi

/-- Coordinate matrix of an orthonormal basis in the standard basis. -/
noncomputable def orthonormalBasisMatrix {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ I)) : Matrix I ι ℝ :=
  (EuclideanSpace.basisFun I ℝ).toBasis.toMatrix b.toBasis

lemma orthonormalBasisMatrix_apply {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ I)) (i : I) (j : ι) :
    orthonormalBasisMatrix b i j = b j i := by
  rfl

theorem orthonormalBasisMatrix_transpose_mul_self
    {ι : Type*} [Fintype ι] [DecidableEq I] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ I)) :
    Matrix.transpose (orthonormalBasisMatrix b) *
      orthonormalBasisMatrix b = 1 := by
  simpa [orthonormalBasisMatrix,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    (EuclideanSpace.basisFun I ℝ).toMatrix_orthonormalBasis_conjTranspose_mul_self b

theorem orthonormalBasisMatrix_mul_transpose
    {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq I]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ I)) :
    orthonormalBasisMatrix b *
      Matrix.transpose (orthonormalBasisMatrix b) = 1 := by
  simpa [orthonormalBasisMatrix,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    (EuclideanSpace.basisFun I ℝ).toMatrix_orthonormalBasis_self_mul_conjTranspose b

/-- The coordinate matrix of a Euclidean matrix operator is obtained by
orthogonal conjugation with the corresponding basis matrix. -/
theorem operatorInBasis_euclideanOperator_eq
    {ι : Type*} [Fintype ι] [DecidableEq I] [DecidableEq ι]
    (A : Matrix I I ℝ)
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ I)) :
    operatorInBasis (euclideanOperator A) b =
      Matrix.transpose (orthonormalBasisMatrix b) * A *
        orthonormalBasisMatrix b := by
  rw [Matrix.mul_assoc]
  ext i j
  rw [operatorInBasis_apply]
  simp only [euclideanOperator, Matrix.mul_apply,
    Matrix.transpose_apply, orthonormalBasisMatrix_apply]
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial]
  change
    (∑ r, (∑ s, A r s * b j s) * b i r) =
      ∑ r, b i r * ∑ s, A r s * b j s
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Matrix-coordinate form of the exact continuation/restart theorem. -/
theorem exists_matrix_exact_completion_basis {k : ℕ} (hk : 0 < k)
    [DecidableEq I]
    (A : Matrix I I ℝ) (hA : Matrix.transpose A = A)
    (X : Matrix I (Fin k) ℝ)
    (hX : Matrix.transpose X * X = 1)
    (T : Matrix (Fin k) (Fin k) ℝ)
    (hTtri : Matrix.UpperTridiagonal T)
    (r : I → ℝ)
    (hr : Matrix.mulVec (Matrix.transpose X) r = 0)
    (hrec : A * X = X * T + lastOuter hk r) :
    ∃ d : ℕ,
      ∃ b : OrthonormalBasis (Fin k ⊕ Fin d) ℝ (EuclideanSpace ℝ I),
        Fintype.card I = k + d ∧
        (∀ i, b (Sum.inl i) = euclideanColumn X i) ∧
        Matrix.SumUpperTridiagonal
          (operatorInBasis (euclideanOperator A) b) ∧
        (∀ i j,
          operatorInBasis (euclideanOperator A) b (Sum.inl i) (Sum.inl j) =
            T i j) := by
  have hx := orthonormal_euclideanColumn X hX
  have hAsymm := euclideanOperator_isSymmetric A hA
  have hr' := matrix_boundary_orthogonal X r hr
  have hrec' := matrix_recurrence_to_columns hk A X T r hrec
  obtain ⟨d, b, hdim, hb, htri, hlead⟩ :=
    exists_exact_tridiagonal_completion_of_pos hk
      (euclideanOperator A) hAsymm (euclideanColumn X) hx T hTtri
      (WithLp.toLp 2 r : EuclideanSpace ℝ I) hr' hrec'
  refine ⟨d, b, ?_, hb, htri, hlead⟩
  simpa using hdim

end FinitePrecisionLanczos
