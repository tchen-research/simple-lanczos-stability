import FinitePrecisionLanczos.Core.Tridiagonalization

/-!
# Completion of an exact initial Lanczos block

This is the exact-linear-algebra half of lem:completion.  It starts with an
orthonormal family satisfying a three-term initial-block recurrence and
constructs a full orthonormal basis in which the operator is tridiagonal.
Breakdowns are handled by restarting inside the invariant orthogonal
complement.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix
open Module Submodule

/-- Position of a prescribed-prefix or tail index in their concatenation. -/
def sumPosition {m d : ℕ} : Fin m ⊕ Fin d → ℕ
  | Sum.inl i => i.1
  | Sum.inr j => m + j.1

/-- Upper-triangular half of tridiagonality on a concatenated index type. -/
def Matrix.SumUpperTridiagonal {m d : ℕ}
    (S : Matrix (Fin m ⊕ Fin d) (Fin m ⊕ Fin d) ℝ) : Prop :=
  ∀ i j, sumPosition i + 1 < sumPosition j → S i j = 0

/-- The span of an indexed vector family. -/
def familySpan {E : Type*} [AddCommMonoid E] [Module ℝ E] {m : ℕ}
    (x : Fin m → E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range x)

lemma family_mem_familySpan {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {m : ℕ} (x : Fin m → E) (i : Fin m) : x i ∈ familySpan x := by
  exact Submodule.subset_span ⟨i, rfl⟩

lemma orthogonal_to_family_mem_perp {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (x : Fin m → E) (p : E)
    (hp : ∀ i, ⟪x i, p⟫_ℝ = 0) : p ∈ (familySpan x)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
      rcases hu with ⟨i, rfl⟩
      exact hp i
  | zero => simp
  | add u v _ _ hu hv => simp [inner_add_left, hu, hv]
  | smul c u _ hu => simp [inner_smul_left, hu]

/-- Coordinate matrix of an operator in an orthonormal basis. -/
noncomputable def operatorInBasis {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
    (A : E →ₗ[ℝ] E) (b : OrthonormalBasis ι ℝ E) : Matrix ι ι ℝ :=
  A.toMatrix b.toBasis b.toBasis

lemma operatorInBasis_apply {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
    (A : E →ₗ[ℝ] E) (b : OrthonormalBasis ι ℝ E) (i j : ι) :
    operatorInBasis A b i j = ⟪b i, A (b j)⟫_ℝ := by
  calc
    _ = b.repr (A (b j)) i := A.toMatrix_apply ..
    _ = ⟪b i, A (b j)⟫_ℝ := b.repr_apply_apply ..

lemma operatorInBasis_transpose {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (b : OrthonormalBasis ι ℝ E) :
    Matrix.transpose (operatorInBasis A b) = operatorInBasis A b := by
  ext i j
  simp only [Matrix.transpose_apply, operatorInBasis_apply]
  exact (hA (b j) (b i)).symm.trans (real_inner_comm _ _)

/-- The exact continuation/restart statement used after the symmetric
correction in eq:symmetric-correction.

The prefix has length m+1, which makes the last prefix index available
without an auxiliary positivity hypothesis.
-/
theorem exists_exact_tridiagonal_completion
    (m : ℕ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (x : Fin (m + 1) → E) (hx : Orthonormal ℝ x)
    (T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hTtri : Matrix.UpperTridiagonal T)
    (r : E) (hr : ∀ i, ⟪x i, r⟫_ℝ = 0)
    (hrec : ∀ j, A (x j) =
      (∑ i, T i j • x i) + if j = Fin.last m then r else 0) :
    ∃ d : ℕ, ∃ b : OrthonormalBasis (Fin (m + 1) ⊕ Fin d) ℝ E,
      finrank ℝ E = (m + 1) + d ∧
      (∀ i, b (Sum.inl i) = x i) ∧
      Matrix.SumUpperTridiagonal (operatorInBasis A b) ∧
      (∀ i j, operatorInBasis A b (Sum.inl i) (Sum.inl j) = T i j) := by
  classical
  let K : Submodule ℝ E := familySpan x
  let P : Submodule ℝ E := Kᗮ
  let d := finrank ℝ P
  have hKdim : finrank ℝ K = m + 1 := by
    change finrank ℝ (familySpan x) = m + 1
    change finrank ℝ (Submodule.span ℝ (Set.range x)) = m + 1
    exact (finrank_span_eq_card hx.linearIndependent).trans (by simp)
  have hdim : finrank ℝ E = (m + 1) + d := by
    have hsum := K.finrank_add_finrank_orthogonal
    simpa [P, d, hKdim, Nat.add_comm] using hsum.symm
  have hrP : r ∈ P := by
    simpa [P, K] using orthogonal_to_family_mem_perp x r hr
  have hlead : ∀ i j,
      ⟪x i, A (x j)⟫_ℝ = T i j := by
    intro i j
    rw [hrec]
    have hxi := orthonormal_iff_ite.mp hx
    have hsum :
        ⟪x i, ∑ l, T l j • x l⟫_ℝ = T i j := by
      rw [inner_sum]
      simp only [inner_smul_right]
      rw [Finset.sum_eq_single i]
      · rw [hxi i i]
        simp
      · intro l _ hli
        rw [hxi i l]
        simp [Ne.symm hli]
      · simp
    have hboundary :
        ⟪x i, if j = Fin.last m then r else 0⟫_ℝ = 0 := by
      split_ifs
      · exact hr i
      · simp
    rw [inner_add_right, hsum, hboundary, add_zero]
  by_cases hd0 : d = 0
  · have hdim0 : finrank ℝ E = (m + 1) + 0 := by
      simpa [hd0] using hdim
    let v : Fin (m + 1) ⊕ Fin 0 → E
      | Sum.inl i => x i
      | Sum.inr j => Fin.elim0 j
    have hv : Orthonormal ℝ v := by
      rw [orthonormal_iff_ite]
      intro i j
      cases i with
      | inl i =>
          cases j with
          | inl j =>
              simpa [v] using orthonormal_iff_ite.mp hx i j
          | inr j => exact Fin.elim0 j
      | inr i => exact Fin.elim0 i
    have hv_univ : Orthonormal ℝ (Set.univ.restrict v) :=
      hv.comp (fun i : (Set.univ : Set (Fin (m + 1) ⊕ Fin 0)) => i.1)
        Subtype.val_injective
    obtain ⟨b, hb⟩ :=
      Orthonormal.exists_orthonormalBasis_extension_of_card_eq
        (𝕜 := ℝ) (E := E) (ι := Fin (m + 1) ⊕ Fin 0)
        (v := v) (s := Set.univ) (by simpa using hdim0) hv_univ
    refine ⟨0, b, hdim0, ?_, ?_, ?_⟩
    · intro i
      simpa [v] using hb (Sum.inl i) (Set.mem_univ _)
    · intro i j hij
      cases i with
      | inl i =>
          cases j with
          | inl j =>
              rw [operatorInBasis_apply, hb _ (Set.mem_univ _),
                hb _ (Set.mem_univ _)]
              simp only [v]
              rw [hlead i j]
              exact hTtri i j hij
          | inr j => exact Fin.elim0 j
      | inr i => exact Fin.elim0 i
    · intro i j
      rw [operatorInBasis_apply, hb _ (Set.mem_univ _),
        hb _ (Set.mem_univ _)]
      exact hlead i j
  · obtain ⟨e, hdSucc⟩ : ∃ e, d = e + 1 :=
      Nat.exists_eq_succ_of_ne_zero hd0
    have hPdim : finrank ℝ P = e + 1 := by
      simpa [d] using hdSucc
    have hdimSucc : finrank ℝ E = (m + 1) + (e + 1) := by
      simpa [hdSucc] using hdim
    let AP : P →ₗ[ℝ] P := compressedOperator A P
    have hAP : AP.IsSymmetric := compressedOperator_isSymmetric A hA P
    let q : P := if hr0 : r = 0 then
        ((stdOrthonormalBasis ℝ P).reindex (finCongr hPdim)) 0
      else (‖r‖⁻¹ : ℝ) • ⟨r, hrP⟩
    have hq : ‖q‖ = 1 := by
      simp only [q]
      split_ifs with hr0
      · exact ((stdOrthonormalBasis ℝ P).reindex (finCongr hPdim)).norm_eq_one 0
      · exact norm_smul_inv_norm hr0
    obtain ⟨bP, hbP0, hbPtri⟩ :=
      exists_orthonormalBasis_upperTridiagonal_with_first e hPdim AP hAP q hq
    let v : Fin (m + 1) ⊕ Fin (e + 1) → E
      | Sum.inl i => x i
      | Sum.inr j => ((bP j : P) : E)
    have hv : Orthonormal ℝ v := by
      rw [orthonormal_iff_ite]
      intro i j
      cases i with
      | inl i =>
          cases j with
          | inl j =>
              simpa [v] using orthonormal_iff_ite.mp hx i j
          | inr j =>
              have hxiK : x i ∈ K := by
                simpa [K] using family_mem_familySpan x i
              have hjP : ((bP j : P) : E) ∈ P := (bP j).property
              have hne : Sum.inl i ≠ (Sum.inr j :
                  Fin (m + 1) ⊕ Fin (e + 1)) := by simp
              simpa [v, hne] using
                Submodule.inner_right_of_mem_orthogonal hxiK hjP
      | inr i =>
          cases j with
          | inl j =>
              have hxjK : x j ∈ K := by
                simpa [K] using family_mem_familySpan x j
              have hiP : ((bP i : P) : E) ∈ P := (bP i).property
              have hne : (Sum.inr i : Fin (m + 1) ⊕ Fin (e + 1)) ≠
                  Sum.inl j := by simp
              simpa [v, hne] using
                Submodule.inner_left_of_mem_orthogonal hxjK hiP
          | inr j =>
              simpa [v] using orthonormal_iff_ite.mp bP.orthonormal i j
    have hv_univ : Orthonormal ℝ (Set.univ.restrict v) :=
      hv.comp
        (fun i : (Set.univ : Set (Fin (m + 1) ⊕ Fin (e + 1))) => i.1)
        Subtype.val_injective
    obtain ⟨b, hb⟩ :=
      Orthonormal.exists_orthonormalBasis_extension_of_card_eq
        (𝕜 := ℝ) (E := E) (ι := Fin (m + 1) ⊕ Fin (e + 1))
        (v := v) (s := Set.univ) (by simpa using hdimSucc) hv_univ
    refine ⟨e + 1, b, hdimSucc, ?_, ?_, ?_⟩
    · intro i
      simpa [v] using hb (Sum.inl i) (Set.mem_univ _)
    · intro i j hij
      rw [operatorInBasis_apply, hb _ (Set.mem_univ _),
        hb _ (Set.mem_univ _)]
      cases i with
      | inl i =>
          cases j with
          | inl j =>
              simp only [v]
              rw [hlead i j]
              exact hTtri i j hij
          | inr j =>
              simp only [v]
              have hcross :
                  ⟪x i, A (((bP j : P) : E))⟫_ℝ =
                    ⟪A (x i), ((bP j : P) : E)⟫_ℝ :=
                (hA (x i) (((bP j : P) : E))).symm
              rw [hcross, hrec]
              have hsumzero :
                  ⟪∑ l, T l i • x l, ((bP j : P) : E)⟫_ℝ = 0 := by
                rw [sum_inner]
                apply Finset.sum_eq_zero
                intro l _
                have hxlK : x l ∈ K := by
                  simpa [K] using family_mem_familySpan x l
                have hjP : ((bP j : P) : E) ∈ P := (bP j).property
                rw [inner_smul_left,
                  Submodule.inner_right_of_mem_orthogonal hxlK hjP, mul_zero]
              rw [inner_add_left, hsumzero, zero_add]
              by_cases hilast : i = Fin.last m
              · subst i
                simp only [if_true]
                have hj0 : j ≠ 0 := by
                  intro hj
                  subst j
                  simp [sumPosition] at hij
                have hjq : ⟪(q : P), bP j⟫_ℝ = 0 := by
                  rw [← hbP0]
                  simpa [Ne.symm hj0] using
                    orthonormal_iff_ite.mp bP.orthonormal 0 j
                by_cases hr0 : r = 0
                · simp [hr0]
                · have hscaled := hjq
                  simp [q, hr0, inner_smul_left,
                    norm_ne_zero_iff.mpr hr0] at hscaled
                  exact hscaled
              · simp [hilast]
      | inr i =>
          cases j with
          | inl j =>
              simp [sumPosition] at hij
              have hjlt := j.isLt
              omega
          | inr j =>
              simp only [v]
              have hijP : i.1 + 1 < j.1 := by
                simp [sumPosition] at hij
                omega
              have hentry := hbPtri i j hijP
              rw [toMatrix_orthonormalBasis_apply] at hentry
              have hproj :
                  ⟪(bP i : P), AP (bP j)⟫_ℝ =
                    ⟪((bP i : P) : E), A (bP j)⟫_ℝ := by
                change
                  ⟪bP i, P.orthogonalProjectionOnto (A (bP j))⟫_ℝ = _
                exact P.inner_orthogonalProjectionOnto_eq_of_mem_left
                  (bP i) (A (bP j))
              exact hproj ▸ hentry
    · intro i j
      rw [operatorInBasis_apply, hb _ (Set.mem_univ _),
        hb _ (Set.mem_univ _)]
      exact hlead i j

/-- Positive-length form of the exact completion theorem, matching the
iteration count used throughout the PDF. -/
theorem exists_exact_tridiagonal_completion_of_pos
    {k : ℕ} (hk : 0 < k) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (x : Fin k → E) (hx : Orthonormal ℝ x)
    (T : Matrix (Fin k) (Fin k) ℝ)
    (hTtri : Matrix.UpperTridiagonal T)
    (r : E) (hr : ∀ i, ⟪x i, r⟫_ℝ = 0)
    (hrec : ∀ j, A (x j) =
      (∑ i, T i j • x i) +
        if j = ⟨k - 1, by omega⟩ then r else 0) :
    ∃ d : ℕ, ∃ b : OrthonormalBasis (Fin k ⊕ Fin d) ℝ E,
      finrank ℝ E = k + d ∧
      (∀ i, b (Sum.inl i) = x i) ∧
      Matrix.SumUpperTridiagonal (operatorInBasis A b) ∧
      (∀ i j, operatorInBasis A b (Sum.inl i) (Sum.inl j) = T i j) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by omega)
  simpa using
    exists_exact_tridiagonal_completion m A hA x hx T hTtri r hr hrec

end FinitePrecisionLanczos
