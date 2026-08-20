import FinitePrecisionLanczos.Core.Measure.FiniteAtomic
import FinitePrecisionLanczos.Lanczos.Greenbaum.Measure









namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator


noncomputable def spectralMass {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (q : I → ℝ) : AtomicMass :=
  ∑ i : I, Finsupp.single (hA.eigenvalues i)
    ((⇑(hA.eigenvectorBasis i) ⬝ᵥ q) ^ 2)


lemma atomicMoment_spectralMass_expansion
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (q : I → ℝ) (m : ℕ) :
    atomicMoment (spectralMass A hA q) m =
      ∑ i : I, ((⇑(hA.eigenvectorBasis i) ⬝ᵥ q) ^ 2) *
        (hA.eigenvalues i) ^ m := by
  classical
  unfold spectralMass
  let g : I → AtomicMass := fun i =>
    Finsupp.single (hA.eigenvalues i)
      ((⇑(hA.eigenvectorBasis i) ⬝ᵥ q) ^ 2)
  let a : I → ℝ := fun i =>
    ((⇑(hA.eigenvectorBasis i) ⬝ᵥ q) ^ 2) *
      (hA.eigenvalues i) ^ m
  change atomicMoment (∑ i : I, g i) m = ∑ i : I, a i
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih, g, a]


lemma mulVec_pow_eigenvectorBasis
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (i : I) (m : ℕ) :
    Matrix.mulVec (A ^ m) ⇑(hA.eigenvectorBasis i) =
      (hA.eigenvalues i) ^ m • ⇑(hA.eigenvectorBasis i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec,
        hA.mulVec_eigenvectorBasis, Matrix.mulVec_smul, ih]
      simp [smul_smul, pow_succ, mul_comm]


lemma sum_eigenvector_coefficients
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (q : I → ℝ) :
    (∑ i : I, (⇑(hA.eigenvectorBasis i) ⬝ᵥ q) •
      ⇑(hA.eigenvectorBasis i)) = q := by
  let b := hA.eigenvectorBasis
  have hsum := b.sum_repr' (WithLp.toLp 2 q : EuclideanSpace ℝ I)
  have hcoef : ∀ i : I,
      ⟪b i, (WithLp.toLp 2 q : EuclideanSpace ℝ I)⟫_ℝ =
        ⇑(b i) ⬝ᵥ q := by
    intro i
    rw [EuclideanSpace.inner_toLp_toLp]
    simp only [star_trivial]
    exact dotProduct_comm _ _
  rw [show hA.eigenvectorBasis = b from rfl]
  rw [show (∑ i : I, (⇑(b i) ⬝ᵥ q) • ⇑(b i)) =
      WithLp.ofLp (∑ i : I,
        ⟪b i, (WithLp.toLp 2 q : EuclideanSpace ℝ I)⟫_ℝ • b i) by
    ext r
    simp [hcoef]]
  rw [hsum]


theorem atomicMoment_spectralMass
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsHermitian) (q : I → ℝ) (m : ℕ) :
    atomicMoment (spectralMass A hA q) m =
      q ⬝ᵥ Matrix.mulVec (A ^ m) q := by
  rw [atomicMoment_spectralMass_expansion]
  have hq := sum_eigenvector_coefficients A hA q
  have hAq : Matrix.mulVec (A ^ m) q =
      ∑ i : I,
        ((⇑(hA.eigenvectorBasis i) ⬝ᵥ q) *
          (hA.eigenvalues i) ^ m) • ⇑(hA.eigenvectorBasis i) := by
    calc
      Matrix.mulVec (A ^ m) q = Matrix.mulVec (A ^ m)
          (∑ i : I, (⇑(hA.eigenvectorBasis i) ⬝ᵥ q) •
            ⇑(hA.eigenvectorBasis i)) := congrArg _ hq.symm
      _ = ∑ i : I,
          ((⇑(hA.eigenvectorBasis i) ⬝ᵥ q) *
            (hA.eigenvalues i) ^ m) • ⇑(hA.eigenvectorBasis i) := by
        rw [Matrix.mulVec_sum]
        apply Fintype.sum_congr
        intro i
        rw [Matrix.mulVec_smul, mulVec_pow_eigenvectorBasis]
        simp [smul_smul]
  rw [hAq, dotProduct_sum]
  apply Fintype.sum_congr
  intro i
  rw [dotProduct_smul]
  rw [dotProduct_comm q ⇑(hA.eigenvectorBasis i)]
  ring

end FinitePrecisionLanczos
