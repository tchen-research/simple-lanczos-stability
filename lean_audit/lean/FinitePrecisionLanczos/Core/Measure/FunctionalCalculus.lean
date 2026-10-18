import FinitePrecisionLanczos.Core.SpectralFrobenius
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace RealInnerProductSpace Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The eigenbasis interpretation of f(A), for any real function on a finite spectrum. -/
theorem cfc_mulVec_eigenvector (A : Matrix I I ℝ) (hA : A.IsHermitian)
    (f : ℝ → ℝ) (i : I) :
    cfc f A *ᵥ ⇑(hA.eigenvectorBasis i) = f (hA.eigenvalues i) • ⇑(hA.eigenvectorBasis i) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA.star_eigenvectorUnitary_mulVec,
    Matrix.diagonal_mulVec_single]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, mul_one]
  have hs : Pi.single i (f (hA.eigenvalues i)) = f (hA.eigenvalues i) • Pi.single i (1 : ℝ) := by
    simp [← Pi.single_smul]
  rw [hs, Matrix.mulVec_smul, hA.eigenvectorUnitary_mulVec]

/-- Spectral integration is the quadratic form of the actual matrix functional calculus. -/
theorem atomicIntegral_spectralMass_cfc (A : Matrix I I ℝ) (hA : A.IsHermitian)
    (q : I → ℝ) (f : ℝ → ℝ) :
    atomicIntegral (spectralMass A hA q) f = q ⬝ᵥ ((cfc f A) *ᵥ q) := by
  rw [atomicIntegral_spectralMass_expansion]
  have hq := sum_eigenvector_coefficients A hA q
  have hAq : (cfc f A) *ᵥ q = ∑ i : I,
      ((⇑(hA.eigenvectorBasis i) ⬝ᵥ q) * f (hA.eigenvalues i)) •
        ⇑(hA.eigenvectorBasis i) := by
    calc
      (cfc f A) *ᵥ q = (cfc f A) *ᵥ
          (∑ i : I, (⇑(hA.eigenvectorBasis i) ⬝ᵥ q) • ⇑(hA.eigenvectorBasis i)) :=
        congrArg _ hq.symm
      _ = _ := by
        rw [Matrix.mulVec_sum]
        apply Fintype.sum_congr
        intro i
        rw [Matrix.mulVec_smul, cfc_mulVec_eigenvector]
        simp [smul_smul]
  rw [hAq, dotProduct_sum]
  apply Fintype.sum_congr
  intro i
  rw [dotProduct_smul, dotProduct_comm q ⇑(hA.eigenvectorBasis i)]
  ring

/-- Parseval on the left and right expresses the Frobenius norm in two orthonormal bases. -/
lemma frobSq_cross_basis (M : Matrix I I ℝ)
    (u v : OrthonormalBasis I ℝ (EuclideanSpace ℝ I)) :
    frobSq M = ∑ j, ∑ i, ⟪u i, indexedMatCLM M (v j)⟫_ℝ ^ 2 := by
  rw [← sum_norm_sq_indexedMatCLM M v]
  exact Fintype.sum_congr _ _ fun j => (u.sum_sq_inner_right _).symm

/-- The cross-basis coefficient identity underlying the Frobenius Lipschitz bound. -/
lemma cfc_cross_difference (A B : Matrix I I ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℝ) (i j : I) :
    ⟪hA.eigenvectorBasis i, indexedMatCLM (cfc f A - cfc f B) (hB.eigenvectorBasis j)⟫_ℝ =
      (f (hA.eigenvalues i) - f (hB.eigenvalues j)) *
        ⟪hA.eigenvectorBasis i, hB.eigenvectorBasis j⟫_ℝ := by
  let u : I → ℝ := ⇑(hA.eigenvectorBasis i)
  let v : I → ℝ := ⇑(hB.eigenvectorBasis j)
  have hAt : (cfc f A)ᵀ = cfc f A :=
    (Matrix.isHermitian_iff_isSymm.mp (show (cfc f A).IsHermitian from cfc_predicate f A)).eq
  have hleft : u ⬝ᵥ ((cfc f A) *ᵥ v) = f (hA.eigenvalues i) * (u ⬝ᵥ v) := by
    rw [← hAt, Matrix.dotProduct_transpose_mulVec, cfc_mulVec_eigenvector A hA f i]
    simp [u, v, dotProduct_smul, dotProduct_comm]
  have hright : u ⬝ᵥ ((cfc f B) *ᵥ v) = f (hB.eigenvalues j) * (u ⬝ᵥ v) := by
    rw [cfc_mulVec_eigenvector B hB f j]
    simp [v, dotProduct_smul]
  have hdot : ⟪hA.eigenvectorBasis i,
      indexedMatCLM (cfc f A - cfc f B) (hB.eigenvectorBasis j)⟫_ℝ =
      u ⬝ᵥ ((cfc f A - cfc f B) *ᵥ v) := by
    simpa [u, v, indexedMatCLM_apply, star_trivial, dotProduct_comm] using
      (EuclideanSpace.inner_toLp_toLp u ((cfc f A - cfc f B) *ᵥ v))
  have huv : ⟪hA.eigenvectorBasis i, hB.eigenvectorBasis j⟫_ℝ = u ⬝ᵥ v := by
    simpa [u, v, star_trivial, dotProduct_comm] using EuclideanSpace.inner_toLp_toLp u v
  rw [hdot, huv, Matrix.sub_mulVec, dotProduct_sub, hleft, hright]
  ring

/-- The full matrix inequality cited in `rem:wasserstein`, not just its scalar consequence. -/
theorem cfc_lipschitz_frobNorm (A B : Matrix I I ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℝ) (hf : OneLipschitz f) :
    frobNorm (cfc f A - cfc f B) ≤ frobNorm (A - B) := by
  apply Real.sqrt_le_sqrt
  rw [frobSq_cross_basis _ hA.eigenvectorBasis hB.eigenvectorBasis,
    frobSq_cross_basis _ hA.eigenvectorBasis hB.eigenvectorBasis]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  rw [cfc_cross_difference, ← eigenbasis_cross_difference A B hA hB]
  have habs : |(f (hA.eigenvalues i) - f (hB.eigenvalues j)) *
      ⟪hA.eigenvectorBasis i, hB.eigenvectorBasis j⟫_ℝ| ≤
      |(hA.eigenvalues i - hB.eigenvalues j) *
        ⟪hA.eigenvectorBasis i, hB.eigenvectorBasis j⟫_ℝ| := by
    simp only [abs_mul]
    exact mul_le_mul_of_nonneg_right (hf _ _) (abs_nonneg _)
  nlinarith [sq_abs ((f (hA.eigenvalues i) - f (hB.eigenvalues j)) *
    ⟪hA.eigenvectorBasis i, hB.eigenvectorBasis j⟫_ℝ),
    sq_abs ((hA.eigenvalues i - hB.eigenvalues j) *
    ⟪hA.eigenvectorBasis i, hB.eigenvectorBasis j⟫_ℝ), abs_nonneg
    ((f (hA.eigenvalues i) - f (hB.eigenvalues j)) *
    ⟪hA.eigenvectorBasis i, hB.eigenvectorBasis j⟫_ℝ)]

/-- The quadratic-form chain in the paper's Wasserstein proof. -/
theorem cfc_quadratic_lipschitz (A B : Matrix I I ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (q : I → ℝ)
    (hq : coordNorm q = 1) (f : ℝ → ℝ) (hf : OneLipschitz f) :
    |q ⬝ᵥ ((cfc f A) *ᵥ q) - q ⬝ᵥ ((cfc f B) *ᵥ q)| ≤
      frobNorm (A - B) := by
  calc
    _ = |q ⬝ᵥ ((cfc f A - cfc f B) *ᵥ q)| := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
    _ ≤ ‖cfc f A - cfc f B‖ := by
      simpa [hq] using abs_dotProduct_mulVec_le (cfc f A - cfc f B) q
    _ ≤ frobNorm (cfc f A - cfc f B) := opNorm_le_frobNorm _
    _ ≤ frobNorm (A - B) := cfc_lipschitz_frobNorm A B hA hB f hf

end FinitePrecisionLanczos
