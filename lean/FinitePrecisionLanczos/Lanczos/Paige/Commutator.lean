import FinitePrecisionLanczos.Lanczos.Assembly
import FinitePrecisionLanczos.Core.Commutator

/-!
# Paige's Gram commutator

This file follows `eq:gram-split`--`lem:gram-commutator`.  The generic exact
commutator is `Core.commutator_of_governing`; here it is instantiated with the
prefix matrices assembled from the arithmetic model, and its error term
receives the explicit bound implied by the local theory.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- Gram defect `Omega_k` in `eq:gram-split`. -/
def Omega : Mat k k := L.Vmatᵀ * L.Vmat - 1

/-- Strict upper triangle `R_k` in `eq:gram-split`. -/
def Rmat : Mat k k := fun i j => if i.1 < j.1 then L.Omega i j else 0

/-- Diagonal near-normalization defect `D_k` in `eq:gram-split`. -/
def Dmat : Mat k k := Matrix.diagonal fun j => L.g (j.1 + 1)

/-- Projected boundary `C_k` in `eq:CG-def`. -/
def Cmat : Mat k k := L.Vmatᵀ * L.boundary

/-- Projected recurrence error `G_k` in `eq:CG-def`. -/
def Gmat : Mat k k := L.Vmatᵀ * L.Fmat - L.Fmatᵀ * L.Vmat

/-- Left side of the upper-triangular identity in `lem:gram-commutator`. -/
def Amat : Mat k k := L.Tmat * L.Rmat - L.Rmat * L.Tmat

/-- Diagonal-near-normalization commutator in `lem:gram-commutator`. -/
def Qmat : Mat k k := L.Tmat * L.Dmat - L.Dmat * L.Tmat

/-- Local-product diagonal `N_k` in `lem:gram-commutator`. -/
def Nmat : Mat k k := Matrix.diagonal fun i => L.p i.1 - L.p (i.1 + 1)

/-- Strict upper triangle of `G_k`. -/
def upG : Mat k k := fun i j => if i.1 < j.1 then L.Gmat i j else 0

/-- Strict upper triangle of `T_kD_k-D_kT_k`. -/
def upQ : Mat k k := fun i j => if i.1 < j.1 then L.Qmat i j else 0

/-- Symmetry of the Gram defect. -/
lemma Omega_transpose : L.Omegaᵀ = L.Omega := by
  rw [Omega, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp

/-- Diagonal entry of the Gram defect. -/
lemma Omega_diag (j : Fin k) : L.Omega j j = L.g (j.1 + 1) := by
  simp only [Omega, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply, Vmat, ofCols, g, vdot, dotProduct]
  simp only [ite_true]

/-- Off-diagonal Gram entries are ordinary column inner products. -/
lemma Omega_offdiag (i j : Fin k) (hij : i ≠ j) :
    L.Omega i j = vdot (L.v (i.1 + 1)) (L.v (j.1 + 1)) := by
  simp [Omega, Vmat, ofCols, Matrix.mul_apply, vdot, dotProduct, hij]

/-- Exact triangular decomposition in `eq:gram-split`. -/
theorem gram_split : L.Omega = L.Rmatᵀ + L.Dmat + L.Rmat := by
  ext i j
  rcases lt_trichotomy i.1 j.1 with hij | hij | hij
  · have hne : i ≠ j := by intro h; simpa [h] using hij.ne
    simp [Rmat, Dmat, hij, not_lt_of_ge hij.le, hne]
  · have hfin : i = j := Fin.ext hij
    subst j
    simp [Rmat, Dmat, L.Omega_diag]
  · have hji : j.1 < i.1 := hij
    have hne : i ≠ j := by intro h; simpa [h] using hji.ne
    have hsym : L.Omega j i = L.Omega i j := by
      have h := congrArg (fun M : Mat k k => M i j) L.Omega_transpose
      simpa using h
    simp [Rmat, Dmat, hji, not_lt_of_ge hji.le, hne, hsym]

/-- The first exact identity in `lem:gram-commutator`, now derived from the
arithmetic model rather than assumed as an interface. -/
theorem gram_commutator :
    L.Tmat * L.Omega - L.Omega * L.Tmat = L.Cmat - L.Cmatᵀ + L.Gmat := by
  exact Core.commutator_of_governing L.H L.Vmat L.Tmat L.boundary L.Fmat
    L.hHsymm L.Tmat_transpose L.governing_matrix

/-- Entrywise representation of the skew recurrence error. -/
lemma Gmat_entry (r s : Fin k) :
    L.Gmat r s = vdot (L.v (r.1 + 1)) (L.f (s.1 + 1))
      - vdot (L.f (r.1 + 1)) (L.v (s.1 + 1)) := by
  simp only [Gmat, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Vmat, Fmat, ofCols, vdot, dotProduct]

/-- Explicit entry bound for `G_k` in `lem:gram-commutator`. -/
theorem Gmat_entry_bound (r s : Fin k) :
    |L.Gmat r s| ≤ (2800 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  have hr := L.recurrence_error_bound (r.1 + 1) (by omega)
    (Nat.succ_le_iff.mpr r.2)
  have hs := L.recurrence_error_bound (s.1 + 1) (by omega)
    (Nat.succ_le_iff.mpr s.2)
  have hvr := L.vnorm_v_le_two (by omega) (Nat.succ_le_iff.mpr r.2)
  have hvs := L.vnorm_v_le_two (by omega) (Nat.succ_le_iff.mpr s.2)
  have hfr : vnorm (L.f (r.1 + 1))
      ≤ (700 * (k : ℝ)) * L.ε * ‖L.H‖ := by
    have hrs : ((r.1 + 1 : ℕ) : ℝ) ≤ k := by
      exact_mod_cast Nat.succ_le_iff.mpr r.2
    have hscale : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
    nlinarith
  have hfs : vnorm (L.f (s.1 + 1))
      ≤ (700 * (k : ℝ)) * L.ε * ‖L.H‖ := by
    have hss : ((s.1 + 1 : ℕ) : ℝ) ≤ k := by
      exact_mod_cast Nat.succ_le_iff.mpr s.2
    have hscale : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
    nlinarith
  have hfirst : |vdot (L.v (r.1 + 1)) (L.f (s.1 + 1))|
      ≤ (1400 * (k : ℝ)) * L.ε * ‖L.H‖ := by
    calc
      |vdot (L.v (r.1 + 1)) (L.f (s.1 + 1))|
          ≤ vnorm (L.v (r.1 + 1)) * vnorm (L.f (s.1 + 1)) := abs_vdot_le _ _
      _ ≤ 2 * ((700 * (k : ℝ)) * L.ε * ‖L.H‖) :=
        mul_le_mul hvr hfs (vnorm_nonneg _) (by positivity)
      _ = (1400 * (k : ℝ)) * L.ε * ‖L.H‖ := by ring
  have hsecond : |vdot (L.f (r.1 + 1)) (L.v (s.1 + 1))|
      ≤ (1400 * (k : ℝ)) * L.ε * ‖L.H‖ := by
    calc
      |vdot (L.f (r.1 + 1)) (L.v (s.1 + 1))|
          ≤ vnorm (L.f (r.1 + 1)) * vnorm (L.v (s.1 + 1)) := abs_vdot_le _ _
      _ ≤ ((700 * (k : ℝ)) * L.ε * ‖L.H‖) * 2 :=
        mul_le_mul hfr hvs (vnorm_nonneg _)
          (mul_nonneg (mul_nonneg (by positivity) L.hε_nonneg) (norm_nonneg _))
      _ = (1400 * (k : ℝ)) * L.ε * ‖L.H‖ := by ring
  rw [L.Gmat_entry]
  calc
    |vdot (L.v (r.1 + 1)) (L.f (s.1 + 1))
        - vdot (L.f (r.1 + 1)) (L.v (s.1 + 1))|
      ≤ |vdot (L.v (r.1 + 1)) (L.f (s.1 + 1))|
          + |vdot (L.f (r.1 + 1)) (L.v (s.1 + 1))| := by
        simpa using abs_sub_le
          (vdot (L.v (r.1 + 1)) (L.f (s.1 + 1))) 0
          (vdot (L.f (r.1 + 1)) (L.v (s.1 + 1)))
    _ ≤ (1400 * (k : ℝ)) * L.ε * ‖L.H‖
          + (1400 * (k : ℝ)) * L.ε * ‖L.H‖ := add_le_add hfirst hsecond
    _ = (2800 * (k : ℝ)) * L.ε * ‖L.H‖ := by ring

/-! ## Upper-triangular extraction -/

private lemma sum_pred_scalar (f : Fin k → ℝ) (j : Fin k) :
    (∑ i : Fin k, if i.1 + 1 = j.1 then f i else 0)
      = if hj : j.1 = 0 then 0 else f ⟨j.1 - 1, by omega⟩ := by
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

private lemma sum_succ_scalar (f : Fin k → ℝ) (j : Fin k) :
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

/-- `T_k R_k-R_k T_k` is upper triangular. -/
lemma Amat_lower_zero (i j : Fin k) (hji : j.1 < i.1) : L.Amat i j = 0 := by
  have hTR : (L.Tmat * L.Rmat) i j = 0 := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro h _
    by_cases hh : h.1 < j.1
    · have hih : i ≠ h := by intro e; subst h; omega
      have hnext : ¬i.1 + 1 = h.1 := by omega
      have hprev : ¬h.1 + 1 = i.1 := by omega
      simp [Tmat, Rmat, hh, hih, hnext, hprev]
    · simp [Rmat, hh]
  have hRT : (L.Rmat * L.Tmat) i j = 0 := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro h _
    by_cases hh : i.1 < h.1
    · have hhj : h ≠ j := by intro e; subst h; omega
      have hnext : ¬h.1 + 1 = j.1 := by omega
      have hprev : ¬j.1 + 1 = h.1 := by omega
      simp [Tmat, Rmat, hh, hhj, hnext, hprev]
    · simp [Rmat, hh]
  simp [Amat, hTR, hRT]

/-- The projected boundary is upper triangular (in fact, last-column supported). -/
lemma Cmat_lower_zero (i j : Fin k) (hji : j.1 < i.1) : L.Cmat i j = 0 := by
  have hj : j.1 + 1 < k := by omega
  simp [Cmat, Matrix.mul_apply, boundary, ofCols, hj]

/-- Skew relation whose strict upper triangle yields the second identity in
`lem:gram-commutator`. -/
lemma Amat_skew :
    L.Amat - L.Amatᵀ = L.Cmat - L.Cmatᵀ + L.Gmat - L.Qmat := by
  have hcomm := L.gram_commutator
  rw [L.gram_split] at hcomm
  have hAT : L.Amatᵀ = L.Rmatᵀ * L.Tmat - L.Tmat * L.Rmatᵀ := by
    simp [Amat, Matrix.transpose_sub, Matrix.transpose_mul, L.Tmat_transpose]
  rw [hAT]
  rw [Amat, Qmat]
  calc
    (L.Tmat * L.Rmat - L.Rmat * L.Tmat)
        - (L.Rmatᵀ * L.Tmat - L.Tmat * L.Rmatᵀ)
      = (L.Tmat * (L.Rmatᵀ + L.Dmat + L.Rmat)
          - (L.Rmatᵀ + L.Dmat + L.Rmat) * L.Tmat)
          - (L.Tmat * L.Dmat - L.Dmat * L.Tmat) := by noncomm_ring
    _ = (L.Cmat - L.Cmatᵀ + L.Gmat)
          - (L.Tmat * L.Dmat - L.Dmat * L.Tmat) := by rw [hcomm]
    _ = L.Cmat - L.Cmatᵀ + L.Gmat - (L.Tmat * L.Dmat - L.Dmat * L.Tmat) := by
      noncomm_ring

/-- Strict-upper entry obtained from the skew relation. -/
lemma Amat_upper_entry (i j : Fin k) (hij : i.1 < j.1) :
    L.Amat i j = L.Cmat i j + L.Gmat i j - L.Qmat i j := by
  have h := congrArg (fun M : Mat k k => M i j) L.Amat_skew
  have hAji := L.Amat_lower_zero j i hij
  have hCji := L.Cmat_lower_zero j i hij
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.transpose_apply] at h
  rw [hAji, hCji] at h
  linarith

/-- Diagonal contribution from `T_k R_k`. -/
private lemma TR_diag (i : Fin k) : (L.Tmat * L.Rmat) i i = L.p i.1 := by
  have hterm : ∀ h : Fin k,
      L.Tmat i h * L.Rmat h i =
        if h.1 + 1 = i.1 then L.β (h.1 + 1) * L.Omega h i else 0 := by
    intro h
    by_cases hp : h.1 < i.1
    · have hne : i ≠ h := by intro e; subst h; omega
      have hforward : ¬i.1 + 1 = h.1 := by omega
      by_cases hback : h.1 + 1 = i.1
      · simp [Tmat, Rmat, hp, hne, hforward, hback]
      · simp [Tmat, Rmat, hp, hne, hforward, hback]
    · have hback : ¬h.1 + 1 = i.1 := by omega
      simp [Rmat, hp, hback]
  simp only [Matrix.mul_apply]
  apply Eq.trans (Finset.sum_congr rfl fun h _ => hterm h)
  rw [sum_pred_scalar (fun h => L.β (h.1 + 1) * L.Omega h i) i]
  by_cases hi0 : i.1 = 0
  · simp [hi0, p, vdot, L.hβ_zero]
  · simp only [hi0, ↓reduceDIte]
    let h : Fin k := ⟨i.1 - 1, by omega⟩
    have hhi : h ≠ i := by
      intro e
      have he := congrArg Fin.val e
      simp [h] at he
      omega
    have hidx : h.1 + 1 = i.1 := by dsimp [h]; omega
    rw [L.Omega_offdiag h i hhi]
    simp only [p, vdot, dotProduct_smul, smul_eq_mul]
    rw [hidx]

/-- Diagonal contribution from `R_k T_k`. -/
private lemma RT_diag (i : Fin k) :
    (L.Rmat * L.Tmat) i i =
      if hi : i.1 + 1 < k then L.p (i.1 + 1) else 0 := by
  have hterm : ∀ h : Fin k,
      L.Rmat i h * L.Tmat h i =
        if i.1 + 1 = h.1 then L.Omega i h * L.β (i.1 + 1) else 0 := by
    intro h
    by_cases hp : i.1 < h.1
    · have hne : h ≠ i := by intro e; subst h; omega
      have hforward : ¬h.1 + 1 = i.1 := by omega
      by_cases hback : i.1 + 1 = h.1
      · simp [Tmat, Rmat, hp, hne, hforward, hback]
      · simp [Tmat, Rmat, hp, hne, hforward, hback]
    · have hback : ¬i.1 + 1 = h.1 := by omega
      simp [Rmat, hp, hback]
  simp only [Matrix.mul_apply]
  apply Eq.trans (Finset.sum_congr rfl fun h _ => hterm h)
  rw [sum_succ_scalar (fun h => L.Omega i h * L.β (i.1 + 1)) i]
  by_cases hi : i.1 + 1 < k
  · simp only [hi, ↓reduceDIte]
    let h : Fin k := ⟨i.1 + 1, hi⟩
    have hih : i ≠ h := by
      intro e
      have he := congrArg Fin.val e
      simp [h] at he
    rw [L.Omega_offdiag i h hih]
    simp only [p, vdot, dotProduct_smul, smul_eq_mul]
    dsimp [h]
    ring
  · simp [hi]

/-- Diagonal entry of the projected boundary. -/
private lemma Cmat_diag (i : Fin k) :
    L.Cmat i i = if hi : i.1 + 1 < k then 0 else L.p (i.1 + 1) := by
  by_cases hi : i.1 + 1 < k
  · simp [Cmat, Matrix.mul_apply, boundary, ofCols, hi]
  · simp only [Cmat, Matrix.mul_apply, Matrix.transpose_apply, boundary, Vmat, ofCols,
      hi, ↓reduceIte, p, vdot, dotProduct, Pi.smul_apply, smul_eq_mul]
    simp

/-- Diagonal bookkeeping in the upper-triangular commutator. -/
lemma Amat_diag (i : Fin k) : L.Amat i i = L.Cmat i i + L.Nmat i i := by
  rw [Amat, Matrix.sub_apply, L.TR_diag, L.RT_diag, L.Cmat_diag]
  simp only [Nmat, Matrix.diagonal_apply_eq]
  split_ifs <;> ring

/-- The second exact identity in `lem:gram-commutator`. -/
theorem upper_commutator :
    L.Amat = L.Cmat + L.Nmat + L.upG - L.upQ := by
  ext i j
  rcases lt_trichotomy i.1 j.1 with hij | hij | hij
  · have hne : i ≠ j := by intro e; subst j; omega
    rw [L.Amat_upper_entry i j hij]
    simp [Nmat, upG, upQ, hij, hne]
  · have hfin : i = j := Fin.ext hij
    subst j
    rw [L.Amat_diag]
    simp [upG, upQ]
  · have hji : j.1 < i.1 := hij
    have hne : i ≠ j := by intro e; subst j; omega
    rw [L.Amat_lower_zero i j hji]
    simp [Nmat, upG, upQ, L.Cmat_lower_zero i j hji, hne, not_lt_of_ge hji.le]

/-- The diagonal-defect term retained in the upper-triangular identity is
supported only on the first superdiagonal, as stated in
`lem:gram-commutator`. -/
theorem upQ_eq_zero_of_not_first_superdiagonal (i j : Fin k)
    (hnot : i.1 + 1 ≠ j.1) : L.upQ i j = 0 := by
  by_cases hij : i.1 < j.1
  · have hne : i ≠ j := by intro h; subst j; omega
    have hback : j.1 + 1 ≠ i.1 := by omega
    rw [upQ, if_pos hij]
    simp [Qmat, Dmat, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Tmat, hne, hnot, hback]
  · simp [upQ, hij]

end LanczosRun
end FinitePrecisionLanczos
