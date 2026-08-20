import FinitePrecisionLanczos.Core.Measure.SpectralWassersteinCore

/-!
# Spectral-measure perturbation in one-Wasserstein distance

This file instantiates the cross-eigenbasis argument for two finite real
symmetric matrices.  It is an optional extension beyond the current PDF.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace RealInnerProductSpace Matrix.Norms.L2Operator

/-- Expansion of a scalar integral against a finite atomic spectral mass. -/
lemma atomicIntegral_spectralMass_expansion
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (q : I → ℝ) (f : ℝ → ℝ) :
    atomicIntegral (spectralMass A hA q) f =
      ∑ i : I, ((⇑(hA.eigenvectorBasis i) ⬝ᵥ q) ^ 2) *
        f (hA.eigenvalues i) := by
  classical
  unfold spectralMass
  let g : I → AtomicMass := fun i =>
    Finsupp.single (hA.eigenvalues i)
      ((⇑(hA.eigenvectorBasis i) ⬝ᵥ q) ^ 2)
  let c : I → ℝ := fun i =>
    ((⇑(hA.eigenvectorBasis i) ⬝ᵥ q) ^ 2) * f (hA.eigenvalues i)
  change atomicIntegral (∑ i : I, g i) f = ∑ i : I, c i
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih, g, c]

/-- Coordinate dot products are the real inner products used by the chosen
Euclidean eigenbasis. -/
lemma inner_eigenvectorBasis_toLp
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (i : I) (q : I → ℝ) :
    ⟪hA.eigenvectorBasis i, (WithLp.toLp 2 q : EuclideanSpace ℝ I)⟫_ℝ =
      ⇑(hA.eigenvectorBasis i) ⬝ᵥ q := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial]
  exact dotProduct_comm _ _

/-- Cross-eigenbasis identity for the difference of two Hermitian matrices.
This is the elementary cross-eigenbasis proof used by the extension. -/
lemma eigenbasis_cross_difference
    {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (i j : I) :
    (hA.eigenvalues i - hB.eigenvalues j) *
        ⟪hA.eigenvectorBasis i, hB.eigenvectorBasis j⟫_ℝ =
      ⟪hA.eigenvectorBasis i,
        indexedMatCLM (A - B) (hB.eigenvectorBasis j)⟫_ℝ := by
  let ui : I → ℝ := ⇑(hA.eigenvectorBasis i)
  let vj : I → ℝ := ⇑(hB.eigenvectorBasis j)
  have hAT : Matrix.transpose A = A := by
    exact (Matrix.isHermitian_iff_isSymm.mp hA).eq
  have hAu := hA.mulVec_eigenvectorBasis i
  have hBv := hB.mulVec_eigenvectorBasis j
  have hAterm : ui ⬝ᵥ Matrix.mulVec A vj =
      hA.eigenvalues i * (ui ⬝ᵥ vj) := by
    calc
      ui ⬝ᵥ Matrix.mulVec A vj =
          ui ⬝ᵥ Matrix.mulVec (Matrix.transpose A) vj := by rw [hAT]
      _ = vj ⬝ᵥ Matrix.mulVec A ui :=
        Matrix.dotProduct_transpose_mulVec A ui vj
      _ = vj ⬝ᵥ (hA.eigenvalues i • ui) := by rw [hAu]
      _ = hA.eigenvalues i * (ui ⬝ᵥ vj) := by
        rw [dotProduct_smul, dotProduct_comm]
        simp [smul_eq_mul]
  have hBterm : ui ⬝ᵥ Matrix.mulVec B vj =
      hB.eigenvalues j * (ui ⬝ᵥ vj) := by
    rw [hBv, dotProduct_smul]
    simp [vj, smul_eq_mul]
  have huv : ⟪hA.eigenvectorBasis i, hB.eigenvectorBasis j⟫_ℝ = ui ⬝ᵥ vj := by
    simpa [ui, vj, star_trivial, dotProduct_comm] using
      (EuclideanSpace.inner_toLp_toLp ui vj)
  have hD : ⟪hA.eigenvectorBasis i,
      indexedMatCLM (A - B) (hB.eigenvectorBasis j)⟫_ℝ =
      ui ⬝ᵥ Matrix.mulVec (A - B) vj := by
    simpa [ui, vj, indexedMatCLM_apply, star_trivial, dotProduct_comm] using
      (EuclideanSpace.inner_toLp_toLp ui (Matrix.mulVec (A - B) vj))
  rw [huv, hD]
  rw [Matrix.sub_mulVec, dotProduct_sub, hAterm, hBterm]
  ring

/-- The test-function estimate underlying the perturbation theorem. -/
theorem spectralIntegral_lipschitz_sub_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (q : I → ℝ) (hq : coordNorm q = 1)
    (f : ℝ → ℝ) (hf : OneLipschitz f) :
    |atomicIntegral (spectralMass A hA q) f -
        atomicIntegral (spectralMass B hB q) f| ≤
      Real.sqrt (Fintype.card I) * ‖A - B‖ := by
  rw [atomicIntegral_spectralMass_expansion,
    atomicIntegral_spectralMass_expansion]
  let qE : EuclideanSpace ℝ I := WithLp.toLp 2 q
  have hqE : ‖qE‖ = 1 := by simpa [qE, coordNorm] using hq
  have hcore := spectralSum_lipschitz_sub_le
    hA.eigenvectorBasis hB.eigenvectorBasis qE hqE
    hA.eigenvalues hB.eigenvalues f hf (indexedMatCLM (A - B))
    (eigenbasis_cross_difference A B hA hB)
  simpa [qE, inner_eigenvectorBasis_toLp, norm_indexedMatCLM] using hcore

/-- Finite-dimensional spectral-measure perturbation lemma. -/
theorem spectralWasserstein_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (q : I → ℝ) (hq : coordNorm q = 1) :
    atomicWasserstein (spectralMass A hA q) (spectralMass B hB q) ≤
      Real.sqrt (Fintype.card I) * ‖A - B‖ := by
  apply atomicWasserstein_le
  intro f hf
  exact spectralIntegral_lipschitz_sub_le A B hA hB q hq f hf

end FinitePrecisionLanczos
