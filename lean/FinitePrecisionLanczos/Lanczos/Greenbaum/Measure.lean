import FinitePrecisionLanczos.Lanczos.Greenbaum.Spectral


namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

lemma blockDiagonal_mul {n k : ℕ} (A B : Mat n n) :
    (blockDiagonal A : Matrix (Fin k × Fin n) (Fin k × Fin n) ℝ) *
      blockDiagonal B = blockDiagonal (A * B) := by
  ext ri sj
  rcases ri with ⟨r, i⟩
  rcases sj with ⟨s, j⟩
  by_cases hrs : r = s
  · subst s
    simp [blockDiagonal, Matrix.mul_apply, Fintype.sum_prod_type]
  · simp [blockDiagonal, Matrix.mul_apply, Fintype.sum_prod_type, hrs]

lemma blockDiagonal_one {n k : ℕ} :
    (blockDiagonal (1 : Mat n n) :
      Matrix (Fin k × Fin n) (Fin k × Fin n) ℝ) = 1 := by
  ext ri sj
  rcases ri with ⟨r, i⟩
  rcases sj with ⟨s, j⟩
  by_cases hrs : r = s
  · subst s
    by_cases hij : i = j
    · subst j
      simp [blockDiagonal]
    · have hp : (r, i) ≠ (r, j) := by
        intro h
        exact hij (Prod.mk.inj h).2
      simp [blockDiagonal, Matrix.one_apply, hij, hp]
  · simp [blockDiagonal, hrs]

lemma blockDiagonal_pow {n k : ℕ} (H : Mat n n) (m : ℕ) :
    (blockDiagonal H : Matrix (Fin k × Fin n) (Fin k × Fin n) ℝ) ^ m =
      blockDiagonal (H ^ m) := by
  induction m with
  | zero => simpa using (blockDiagonal_one (n := n) (k := k)).symm
  | succ m ih =>
      rw [pow_succ, pow_succ, ih, blockDiagonal_mul]

lemma blockDiagonal_mulVec_physicalFirst {n k : ℕ} (hk : 0 < k)
    (A : Mat n n) (V : Mat n k) :
    Matrix.mulVec (blockDiagonal A) (physicalFirst hk V) =
      physicalFirst hk (A * V) := by
  ext ri
  rcases ri with ⟨r, i⟩
  rw [blockDiagonal_mulVec_apply]
  by_cases hr : r.1 = 0
  · simp [physicalFirst, hr, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · simp [physicalFirst, hr, Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma dotProduct_physicalFirst {n k : ℕ} (hk : 0 < k) (V W : Mat n k) :
    physicalFirst hk V ⬝ᵥ physicalFirst hk W =
      (fun i => V i (⟨0, hk⟩ : Fin k)) ⬝ᵥ
        (fun i => W i (⟨0, hk⟩ : Fin k)) := by
  classical
  simp only [physicalFirst, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (0 : Fin (k + 1))]
  · simp
  · intro r _hr hrne
    have hr0 : r.1 ≠ 0 := by
      intro h
      apply hrne
      exact Fin.ext h
    simp [hr0]
  · simp

theorem physicalFirst_block_moment {n k : ℕ} (hk : 0 < k)
    (H : Mat n n) (V : Mat n k) (m : ℕ) :
    physicalFirst hk V ⬝ᵥ
        Matrix.mulVec (blockDiagonal H ^ m) (physicalFirst hk V) =
      (fun i => V i (⟨0, hk⟩ : Fin k)) ⬝ᵥ
        Matrix.mulVec (H ^ m) (fun i => V i (⟨0, hk⟩ : Fin k)) := by
  rw [blockDiagonal_pow, blockDiagonal_mulVec_physicalFirst,
    dotProduct_physicalFirst]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

noncomputable def normalizedStart : Vec n :=
  fun i => L.normalizedV i (⟨0, L.hk_pos⟩ : Fin k)

theorem greenbaumStart_unit : coordNorm L.greenbaumStart = 1 := by
  rw [← L.greenbaumX_first_eq_start,
    coordNorm_mulVec_eq_of_gram _ L.greenbaumX_orthonormal, firstCoord, coordNorm]
  simp

theorem greenbaum_starting_moment (m : ℕ) :
    L.greenbaumStart ⬝ᵥ (L.greenbaumBlockOperator ^ m) *ᵥ L.greenbaumStart =
      L.normalizedStart ⬝ᵥ (L.H ^ m) *ᵥ L.normalizedStart :=
  physicalFirst_block_moment L.hk_pos L.H L.normalizedV m

end LanczosRun
end FinitePrecisionLanczos
