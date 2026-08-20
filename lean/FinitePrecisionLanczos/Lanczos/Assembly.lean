import FinitePrecisionLanczos.Lanczos.Bounds

/-!
# Prefix matrices and the stacked governing relation

The declarations here assemble the one-based run into the matrices appearing
in `eq:governing`.  Each definition is columnwise, so the proof of the stacked
identity can be checked directly against `LanczosRun.governing_column`.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- `V_k = [v_1, ..., v_k]` in `eq:governing`. -/
def Vmat : Mat n k := ofCols fun j => L.v (j.1 + 1)

/-- `F_k = [f_1, ..., f_k]` in `eq:governing`. -/
def Fmat : Mat n k := ofCols fun j => L.f (j.1 + 1)

/-- Computed symmetric tridiagonal `T_k` from `eq:governing`.

The three summands are respectively the diagonal, subdiagonal, and
superdiagonal.  Their additive form makes the matrix-product audit
transparent. -/
def Tmat : Mat k k := fun i j =>
  (if i = j then L.α (i.1 + 1) else 0)
    + (if i.1 + 1 = j.1 then L.β (i.1 + 1) else 0)
    + (if j.1 + 1 = i.1 then L.β (j.1 + 1) else 0)

/-- Exact symmetry of the computed coefficient matrix. -/
theorem Tmat_transpose : L.Tmatᵀ = L.Tmat := by
  ext i j
  simp only [Tmat, Matrix.transpose_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := Ne.symm hij
    simp only [if_neg hij, if_neg hji, zero_add]
    by_cases hforward : i.1 + 1 = j.1
    · have hbackward : ¬j.1 + 1 = i.1 := by omega
      simp [hforward, hbackward]
    · by_cases hbackward : j.1 + 1 = i.1
      · simp [hforward, hbackward]
      · simp [hforward, hbackward]

/-- A finite sum supported at the unique predecessor of `j`. -/
private lemma sum_pred (f : Fin k → ℝ) (j : Fin k) :
    (∑ i : Fin k, if i.1 + 1 = j.1 then f i else 0)
      = if hj : j.1 = 0 then 0
        else f ⟨j.1 - 1, by omega⟩ := by
  by_cases hj : j.1 = 0
  · simp only [hj, ↓reduceDIte]
    apply Finset.sum_eq_zero
    intro i _
    simp
  · simp only [hj, ↓reduceDIte]
    let p : Fin k := ⟨j.1 - 1, by omega⟩
    have hp : p.1 + 1 = j.1 := by dsimp [p]; omega
    rw [Finset.sum_eq_single p]
    · simp only [hp, if_true]
      congr 1
    · intro i _ hip
      have hne : ¬i.1 + 1 = j.1 := by
        intro h
        apply hip
        apply Fin.ext
        dsimp [p]
        omega
      simp [hne]
    · simp

/-- A finite sum supported at the unique successor of `j`. -/
private lemma sum_succ (f : Fin k → ℝ) (j : Fin k) :
    (∑ i : Fin k, if j.1 + 1 = i.1 then f i else 0)
      = if hj : j.1 + 1 < k then f ⟨j.1 + 1, hj⟩ else 0 := by
  by_cases hj : j.1 + 1 < k
  · simp only [hj, ↓reduceDIte]
    let s : Fin k := ⟨j.1 + 1, hj⟩
    rw [Finset.sum_eq_single s]
    · simp [s]
    · intro i _ his
      have hne : ¬j.1 + 1 = i.1 := by
        intro h
        apply his
        apply Fin.ext
        dsimp [s]
        omega
      simp [hne]
    · simp
  · simp only [hj, ↓reduceDIte]
    apply Finset.sum_eq_zero
    intro i _
    have hne : ¬j.1 + 1 = i.1 := by omega
    simp [hne]

/-- Coordinate form of the tridiagonal action.  This is the row identity
used to obtain `eq:leading-coefficient` for every leading prefix. -/
theorem Tmat_mulVec_apply (y : Vec k) (i : Fin k) :
    (L.Tmat *ᵥ y) i =
      L.α (i.1 + 1) * y i
      + (if hi : i.1 = 0 then 0
          else L.β i.1 * y ⟨i.1 - 1, by omega⟩)
      + (if hi : i.1 + 1 < k then
          L.β (i.1 + 1) * y ⟨i.1 + 1, hi⟩ else 0) := by
  simp only [Matrix.mulVec, dotProduct, Tmat, add_mul, Finset.sum_add_distrib]
  have hdiag :
      (∑ j : Fin k, (if i = j then L.α (i.1 + 1) else 0) * y j)
        = L.α (i.1 + 1) * y i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  have hsucc :
      (∑ j : Fin k,
        (if i.1 + 1 = j.1 then L.β (i.1 + 1) else 0) * y j)
        = if hi : i.1 + 1 < k then
            L.β (i.1 + 1) * y ⟨i.1 + 1, hi⟩ else 0 := by
    simp_rw [ite_mul, zero_mul]
    rw [sum_succ (fun j => L.β (i.1 + 1) * y j) i]
  have hpred :
      (∑ j : Fin k,
        (if j.1 + 1 = i.1 then L.β (j.1 + 1) else 0) * y j)
        = if hi : i.1 = 0 then 0
          else L.β i.1 * y ⟨i.1 - 1, by omega⟩ := by
    simp_rw [ite_mul, zero_mul]
    rw [sum_pred (fun j => L.β (j.1 + 1) * y j) i]
    by_cases hi : i.1 = 0
    · simp [hi]
    · simp only [hi, ↓reduceDIte]
      have hsub : i.1 - 1 + 1 = i.1 := by omega
      rw [hsub]
  rw [hdiag, hsucc, hpred]
  ring

/-- The part of `V_k T_k` contained in the first `k` columns, written
columnwise before the tridiagonal matrix is introduced. -/
def within : Mat n k := ofCols fun j =>
  L.β j.1 • L.v j.1 + L.α (j.1 + 1) • L.v (j.1 + 1) +
    if j.1 + 1 < k then L.β (j.1 + 1) • L.v (j.1 + 2) else 0

/-- Last-column boundary `β_k v_{k+1} e_kᵀ` in `eq:governing`. -/
def boundary : Mat n k := ofCols fun j =>
  if j.1 + 1 < k then 0 else L.β (j.1 + 1) • L.v (j.1 + 2)

/-- Column expansion of `V_k T_k`; this is the matrix-assembly step that
was missing from the earlier `simpler Paige/lean` development. -/
theorem Vmat_mul_Tmat : L.Vmat * L.Tmat = L.within := by
  ext a j
  simp only [Matrix.mul_apply, Vmat, ofCols, Tmat, within, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hdiag :
      (∑ i : Fin k, L.v (i.1 + 1) a * if i = j then L.α (i.1 + 1) else 0)
        = L.α (j.1 + 1) * L.v (j.1 + 1) a := by
    rw [Finset.sum_eq_single j]
    · simp; ring
    · intro i _ hij
      simp [hij]
    · simp
  have hpred :
      (∑ i : Fin k, L.v (i.1 + 1) a *
        if i.1 + 1 = j.1 then L.β (i.1 + 1) else 0)
        = L.β j.1 * L.v j.1 a := by
    simp_rw [mul_ite, mul_zero]
    rw [sum_pred (fun i => L.v (i.1 + 1) a * L.β (i.1 + 1)) j]
    by_cases hj0 : j.1 = 0
    · simp [hj0, L.hβ_zero]
    · simp only [hj0, ↓reduceDIte]
      have hsub : j.1 - 1 + 1 = j.1 := by omega
      rw [hsub]
      ring
  have hsucc :
      (∑ i : Fin k, L.v (i.1 + 1) a *
        if j.1 + 1 = i.1 then L.β (j.1 + 1) else 0)
        = if hj : j.1 + 1 < k
          then L.β (j.1 + 1) * L.v (j.1 + 2) a else 0 := by
    simp_rw [mul_ite, mul_zero]
    rw [sum_succ (fun i => L.v (i.1 + 1) a * L.β (j.1 + 1)) j]
    split_ifs <;> ring
  rw [hdiag, hpred, hsucc]
  split_ifs <;> simp
  <;> ring

/-- Stacked form of the column recurrence, prior to identifying `within`
with `V_k T_k`. -/
theorem governing_stacked_columns :
    L.H * L.Vmat = L.within + L.boundary + L.Fmat := by
  ext a j
  have hcol := L.governing_column j.1 j.2
  change (L.H *ᵥ L.v (j.1 + 1)) a =
    ((L.β j.1 • L.v j.1 + L.α (j.1 + 1) • L.v (j.1 + 1) +
        (if j.1 + 1 < k then L.β (j.1 + 1) • L.v (j.1 + 2) else 0)) +
      (if j.1 + 1 < k then 0 else L.β (j.1 + 1) • L.v (j.1 + 2)) +
      L.f (j.1 + 1)) a
  rw [hcol]
  split_ifs <;> simp
  <;> abel

/-- Full block recurrence `eq:governing`. -/
theorem governing_matrix :
    L.H * L.Vmat = L.Vmat * L.Tmat + L.boundary + L.Fmat := by
  rw [L.Vmat_mul_Tmat]
  exact L.governing_stacked_columns

/-- Operator-norm consequence of `thm:local-errors`, with explicit constant
`700 k²`. -/
theorem Fmat_bound :
    ‖L.Fmat‖ ≤ (700 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖ := by
  have hcol : ∀ j : Fin k,
      vnorm (L.f (j.1 + 1)) ≤ (700 * (k : ℝ)) * L.ε * ‖L.H‖ := by
    intro j
    have hj := L.recurrence_error_bound (j.1 + 1) (by omega) (Nat.succ_le_iff.mpr j.2)
    have hs : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
    calc
      vnorm (L.f (j.1 + 1))
          ≤ (700 * ((j.1 + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖ := hj
      _ ≤ (700 * (k : ℝ)) * L.ε * ‖L.H‖ := by
        have hjk : ((j.1 + 1 : ℕ) : ℝ) ≤ k := by
          exact_mod_cast Nat.succ_le_iff.mpr j.2
        nlinarith
  calc
    ‖L.Fmat‖ ≤ ∑ j : Fin k, vnorm (L.f (j.1 + 1)) := norm_ofCols_le_sum _
    _ ≤ ∑ _j : Fin k, (700 * (k : ℝ)) * L.ε * ‖L.H‖ :=
      Finset.sum_le_sum fun j _ => hcol j
    _ = (k : ℝ) * ((700 * (k : ℝ)) * L.ε * ‖L.H‖) := by simp
    _ = (700 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖ := by ring

end LanczosRun
end FinitePrecisionLanczos
