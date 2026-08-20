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
  rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
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


theorem orthogonalConjugate_pow {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℝ) (U : Matrix I J ℝ)
    (hUtU : Matrix.transpose U * U = 1)
    (hUUt : U * Matrix.transpose U = 1) (m : ℕ) :
    (Matrix.transpose U * A * U) ^ m =
      Matrix.transpose U * A ^ m * U := by
  induction m with
  | zero =>
      rw [pow_zero, pow_zero, Matrix.mul_one, hUtU]
  | succ m ih =>
      rw [pow_succ, pow_succ, ih]
      calc
        (Matrix.transpose U * A ^ m * U) *
            (Matrix.transpose U * A * U) =
            Matrix.transpose U * A ^ m *
              (U * Matrix.transpose U) * A * U := by
          simp only [Matrix.mul_assoc]
        _ = Matrix.transpose U * (A ^ m * A) * U := by
          rw [hUUt]
          simp [Matrix.mul_assoc]



theorem orthogonalConjugate_moment {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℝ) (U : Matrix I J ℝ)
    (hUtU : Matrix.transpose U * U = 1)
    (hUUt : U * Matrix.transpose U = 1) (q : J → ℝ) (m : ℕ) :
    q ⬝ᵥ Matrix.mulVec ((Matrix.transpose U * A * U) ^ m) q =
      Matrix.mulVec U q ⬝ᵥ Matrix.mulVec (A ^ m) (Matrix.mulVec U q) := by
  rw [orthogonalConjugate_pow A U hUtU hUUt]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact (Matrix.dotProduct_transpose_mulVec U q
    (Matrix.mulVec (A ^ m) (Matrix.mulVec U q))).trans
      (dotProduct_comm _ _)

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)


noncomputable def normalizedStart : Vec n :=
  fun i => L.normalizedV i (⟨0, L.hk_pos⟩ : Fin k)

lemma normalizedStart_eq :
    L.normalizedStart =
      (L.columnNorm (⟨0, L.hk_pos⟩ : Fin k))⁻¹ • L.v 1 := by
  exact L.normalizedV_column (⟨0, L.hk_pos⟩ : Fin k)

theorem normalizedStart_unit : vnorm L.normalizedStart = 1 := by
  exact L.normalizedV_unit (⟨0, L.hk_pos⟩ : Fin k)



theorem greenbaum_starting_moment {d : ℕ}
    (U : Matrix (Fin k × Fin n) (Fin k ⊕ Fin d) ℝ)
    (hUtU : Matrix.transpose U * U = 1)
    (hUUt : U * Matrix.transpose U = 1)
    (hprefix : ∀ r i, U r (Sum.inl i) = L.greenbaumX r i)
    (m : ℕ) :
    completionFirst L.hk_pos d ⬝ᵥ
        Matrix.mulVec
          ((Matrix.transpose U * L.greenbaumBlockOperator * U) ^ m)
          (completionFirst L.hk_pos d) =
      L.normalizedStart ⬝ᵥ Matrix.mulVec (L.H ^ m) L.normalizedStart := by
  have hUfirst :
      Matrix.mulVec U (completionFirst L.hk_pos d) =
        physicalFirst L.hk_pos L.normalizedV := by
    calc
      Matrix.mulVec U (completionFirst L.hk_pos d) =
          fun r => U r (Sum.inl (⟨0, L.hk_pos⟩ : Fin k)) :=
        L.mulVec_completionFirst U
      _ = fun r => L.greenbaumX r (⟨0, L.hk_pos⟩ : Fin k) := by
        funext r
        exact hprefix r (⟨0, L.hk_pos⟩ : Fin k)
      _ = physicalFirst L.hk_pos L.normalizedV := L.greenbaumX_first_column
  rw [greenbaumBlockOperator]
  rw [orthogonalConjugate_moment (blockDiagonal L.H) U hUtU hUUt]
  rw [hUfirst]
  exact physicalFirst_block_moment L.hk_pos L.H L.normalizedV m

end LanczosRun
end FinitePrecisionLanczos
