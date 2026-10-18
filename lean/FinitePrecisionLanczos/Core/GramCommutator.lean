import FinitePrecisionLanczos.Core.Commutator
import FinitePrecisionLanczos.Core.DilationRecurrence


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n k : ℕ}

def Tridiagonal (T : Mat k k) : Prop :=
  ∀ i j : Fin k, i.1 + 1 < j.1 ∨ j.1 + 1 < i.1 → T i j = 0

lemma lastOuter_apply {ι : Type*} (hk : 0 < k) (x : ι → ℝ) (i : ι) (j : Fin k) :
    lastOuter hk x i j = if j.1 + 1 = k then x i else 0 := by
  simp only [lastOuter, Matrix.vecMulVec, lastCoord, Matrix.of_apply,
    Pi.single_apply, Fin.ext_iff]
  split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | ring


section Products

variable {T Y : Mat k k}

lemma tridiag_mul_strictUpper_lower (hT : Tridiagonal T) (hY : StrictUpper Y)
    (i j : Fin k) (hji : j.1 < i.1) : (T * Y) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases hmj : m.1 < j.1
  · rw [hT i m (Or.inr (by omega)), zero_mul]
  · rw [hY m j hmj, mul_zero]

lemma strictUpper_mul_tridiag_lower (hT : Tridiagonal T) (hY : StrictUpper Y)
    (i j : Fin k) (hji : j.1 < i.1) : (Y * T) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases him : i.1 < m.1
  · rw [hT m j (Or.inr (by omega)), mul_zero]
  · rw [hY i m him, zero_mul]

lemma tridiag_mul_strictUpper_diag (hT : Tridiagonal T) (hY : StrictUpper Y)
    (i : Fin k) :
    (T * Y) i i =
      if h : i.1 = 0 then 0
      else T i ⟨i.1 - 1, by omega⟩ * Y ⟨i.1 - 1, by omega⟩ i := by
  rw [Matrix.mul_apply]
  split_ifs with h
  · apply Finset.sum_eq_zero
    intro m _
    rw [hY m i (by omega), mul_zero]
  · rw [Finset.sum_eq_single (⟨i.1 - 1, by omega⟩ : Fin k)]
    · intro m _ hm
      by_cases hmi : m.1 < i.1
      · have hne : m.1 ≠ i.1 - 1 := fun h' => hm (Fin.ext h')
        rw [hT i m (Or.inr (by omega)), zero_mul]
      · rw [hY m i hmi, mul_zero]
    · simp

lemma strictUpper_mul_tridiag_diag (hT : Tridiagonal T) (hY : StrictUpper Y)
    (i : Fin k) :
    (Y * T) i i =
      if h : i.1 + 1 < k then Y i ⟨i.1 + 1, h⟩ * T ⟨i.1 + 1, h⟩ i else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨i.1 + 1, h⟩ : Fin k)]
    · intro m _ hm
      by_cases him : i.1 < m.1
      · have hne : m.1 ≠ i.1 + 1 := fun h' => hm (Fin.ext h')
        rw [hT m i (Or.inr (by omega)), mul_zero]
      · rw [hY i m him, zero_mul]
    · simp
  · apply Finset.sum_eq_zero
    intro m _
    rw [hY i m (by have := m.2; omega), zero_mul]

end Products


structure GramRecurrence (n k : ℕ) where
  hk : 0 < k
  A : Mat n n
  T : Mat k k
  W : Mat n k
  b : Vec n
  Z : Mat n k
  Y : Mat k k
  Δ : Vec k
  hA : Aᵀ = A
  hT : Tᵀ = T
  htri : Tridiagonal T
  hrec : A * W = W * T + lastOuter hk b + Z
  hY : StrictUpper Y
  hgram : Wᵀ * W = 1 + Yᵀ + Matrix.diagonal Δ + Y

namespace GramRecurrence

variable (G : GramRecurrence n k)

def col (j : Fin k) : Vec n := fun r => G.W r j

noncomputable def N : Mat k k :=
  G.T * G.Y - G.Y * G.T - lastOuter G.hk (G.Wᵀ *ᵥ G.b)

lemma T_symm (i j : Fin k) : G.T i j = G.T j i := by
  calc
    G.T i j = G.Tᵀ j i := rfl
    _ = G.T j i := by rw [G.hT]

lemma gram_apply (i j : Fin k) :
    (G.Wᵀ * G.W) i j = vdot (G.col i) (G.col j) := by
  simp [Matrix.mul_apply, vdot, dotProduct, col]

lemma Y_apply (i j : Fin k) (hij : i.1 < j.1) :
    G.Y i j = vdot (G.col i) (G.col j) := by
  have h := congrFun (congrFun G.hgram i) j
  have hne : i ≠ j := by intro h'; subst h'; omega
  have hji : G.Y j i = 0 := G.hY j i (by omega)
  rw [G.gram_apply] at h
  simp [Matrix.add_apply, hne,
    Matrix.transpose_apply, hji] at h
  exact h.symm

lemma mulVec_b_apply (i : Fin k) : (G.Wᵀ *ᵥ G.b) i = vdot (G.col i) G.b := by
  simp [Matrix.mulVec, vdot, dotProduct, col]

theorem gram_commutator_full :
    G.T * (G.Wᵀ * G.W) - (G.Wᵀ * G.W) * G.T =
      lastOuter G.hk (G.Wᵀ *ᵥ G.b) - (lastOuter G.hk (G.Wᵀ *ᵥ G.b))ᵀ +
        (G.Wᵀ * G.Z - G.Zᵀ * G.W) := by
  have h := Core.commutator_of_governing G.A G.W G.T (lastOuter G.hk G.b) G.Z
    G.hA G.hT G.hrec
  rw [mul_lastOuter] at h
  rw [← h]
  noncomm_ring

theorem N_skew :
    G.N - G.Nᵀ =
      G.Wᵀ * G.Z - G.Zᵀ * G.W -
        (G.T * Matrix.diagonal G.Δ - Matrix.diagonal G.Δ * G.T) := by
  have h := G.gram_commutator_full
  rw [G.hgram] at h
  have hNt : G.Nᵀ = G.Yᵀ * G.T - G.T * G.Yᵀ -
      (lastOuter G.hk (G.Wᵀ *ᵥ G.b))ᵀ := by
    simp only [N, Matrix.transpose_sub, Matrix.transpose_mul, G.hT]
  rw [hNt]
  calc
    G.N - (G.Yᵀ * G.T - G.T * G.Yᵀ - (lastOuter G.hk (G.Wᵀ *ᵥ G.b))ᵀ) =
        (G.T * (1 + G.Yᵀ + Matrix.diagonal G.Δ + G.Y) -
            (1 + G.Yᵀ + Matrix.diagonal G.Δ + G.Y) * G.T) -
          (lastOuter G.hk (G.Wᵀ *ᵥ G.b) - (lastOuter G.hk (G.Wᵀ *ᵥ G.b))ᵀ) -
          (G.T * Matrix.diagonal G.Δ - Matrix.diagonal G.Δ * G.T) := by
      simp only [N]
      noncomm_ring
    _ = _ := by rw [h]; abel

theorem N_upper : Upper G.N := by
  intro i j hji
  have hj : ¬j.1 + 1 = k := by have := i.2; omega
  simp only [N, Matrix.sub_apply,
    tridiag_mul_strictUpper_lower G.htri G.hY i j hji,
    strictUpper_mul_tridiag_lower G.htri G.hY i j hji, lastOuter_apply, hj,
    if_false, sub_zero]

theorem N_diag (i : Fin k) :
    G.N i i =
      (if h : i.1 = 0 then 0
        else G.T ⟨i.1 - 1, by omega⟩ i *
          vdot (G.col ⟨i.1 - 1, by omega⟩) (G.col i)) -
      (if h : i.1 + 1 < k then
          G.T i ⟨i.1 + 1, h⟩ * vdot (G.col i) (G.col ⟨i.1 + 1, h⟩)
        else vdot (G.col i) G.b) := by
  rw [N, Matrix.sub_apply, Matrix.sub_apply,
    tridiag_mul_strictUpper_diag G.htri G.hY,
    strictUpper_mul_tridiag_diag G.htri G.hY, lastOuter_apply, G.mulVec_b_apply]
  by_cases h0 : i.1 = 0 <;> by_cases h1 : i.1 + 1 < k
  · have h1' : ¬i.1 + 1 = k := by omega
    simp only [dif_pos h0, dif_pos h1, if_neg h1']
    rw [G.Y_apply i ⟨i.1 + 1, h1⟩ (show i.1 < i.1 + 1 by omega), G.T_symm ⟨i.1 + 1, h1⟩ i]
    ring
  · have h1' : i.1 + 1 = k := by omega
    simp only [dif_pos h0, dif_neg h1, if_pos h1']
    ring
  · have h1' : ¬i.1 + 1 = k := by omega
    simp only [dif_neg h0, dif_pos h1, if_neg h1']
    rw [G.Y_apply i ⟨i.1 + 1, h1⟩ (show i.1 < i.1 + 1 by omega),
      G.Y_apply _ i (show i.1 - 1 < i.1 by omega),
      G.T_symm ⟨i.1 + 1, h1⟩ i, G.T_symm i ⟨i.1 - 1, by omega⟩]
    ring
  · have h1' : i.1 + 1 = k := by omega
    simp only [dif_neg h0, dif_neg h1, if_pos h1']
    rw [G.Y_apply _ i (show i.1 - 1 < i.1 by omega),
      G.T_symm i ⟨i.1 - 1, by omega⟩]
    ring


theorem N_diag_bound (P : ℝ)
    (hadj : ∀ i j : Fin k, i.1 + 1 = j.1 →
      |G.T i j * vdot (G.col i) (G.col j)| ≤ P)
    (hbd : ∀ i : Fin k, i.1 + 1 = k → |vdot (G.col i) G.b| ≤ P)
    (i : Fin k) : |G.N i i| ≤ 2 * P := by
  have hP : 0 ≤ P := (abs_nonneg _).trans
    (hbd ⟨k - 1, by have := G.hk; omega⟩ (by have := G.hk; simp; omega))
  have key : ∀ a c : ℝ, |a| ≤ P → |c| ≤ P → |a - c| ≤ 2 * P :=
    fun a c ha hc => (abs_sub a c).trans (by linarith)
  rw [G.N_diag]
  split_ifs with h0 h1 h1
  · exact key _ _ (by simpa using hP) (hadj _ _ rfl)
  · exact key _ _ (by simpa using hP) (hbd i (by omega))
  · exact key _ _ (hadj _ _ (by simp; omega)) (hadj _ _ rfl)
  · exact key _ _ (hadj _ _ (by simp; omega)) (hbd i (by omega))

theorem N_strictUpper_entry_bound (c D : ℝ)
    (hcol : ∀ l : Fin k, vnorm (G.col l) ≤ c)
    (hΔ : ∀ i j : Fin k, i.1 + 1 = j.1 → |G.T i j * (G.Δ j - G.Δ i)| ≤ D)
    (hD : 0 ≤ D) (i j : Fin k) (hij : i.1 < j.1) :
    |G.N i j| ≤ 2 * c * ‖G.Z‖ + D := by
  have hlow : G.N j i = 0 := G.N_upper j i hij
  have hskew := congrFun (congrFun G.N_skew i) j
  simp only [Matrix.sub_apply, Matrix.transpose_apply, hlow, sub_zero] at hskew
  rw [hskew]
  have hc0 : 0 ≤ c := (vnorm_nonneg _).trans (hcol i)
  have h1 : |(G.Wᵀ * G.Z) i j| ≤ c * ‖G.Z‖ := by
    have he : (G.Wᵀ * G.Z) i j = vdot (G.col i) (fun r => G.Z r j) := by
      simp [Matrix.mul_apply, vdot, dotProduct, col]
    rw [he]
    exact (abs_vdot_le _ _).trans
      (mul_le_mul (hcol i) (vnorm_col_le_opNorm _ _) (vnorm_nonneg _) hc0)
  have h2 : |(G.Zᵀ * G.W) i j| ≤ c * ‖G.Z‖ := by
    have he : (G.Zᵀ * G.W) i j = vdot (fun r => G.Z r i) (G.col j) := by
      simp [Matrix.mul_apply, vdot, dotProduct, col]
    rw [he, mul_comm]
    exact (abs_vdot_le _ _).trans
      (mul_le_mul (vnorm_col_le_opNorm _ _) (hcol j) (vnorm_nonneg _)
        (norm_nonneg _))
  have h3 : |(G.T * Matrix.diagonal G.Δ) i j - (Matrix.diagonal G.Δ * G.T) i j|
      ≤ D := by
    have he : (G.T * Matrix.diagonal G.Δ) i j - (Matrix.diagonal G.Δ * G.T) i j =
        G.T i j * (G.Δ j - G.Δ i) := by
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
      ring
    rw [he]
    by_cases hadj : i.1 + 1 = j.1
    · exact hΔ i j hadj
    · rw [G.htri i j (Or.inl (by omega)), zero_mul, abs_zero]
      exact hD
  calc
    |(G.Wᵀ * G.Z) i j - (G.Zᵀ * G.W) i j -
        ((G.T * Matrix.diagonal G.Δ) i j - (Matrix.diagonal G.Δ * G.T) i j)| ≤
      |(G.Wᵀ * G.Z) i j| + |(G.Zᵀ * G.W) i j| +
        |(G.T * Matrix.diagonal G.Δ) i j - (Matrix.diagonal G.Δ * G.T) i j| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ c * ‖G.Z‖ + c * ‖G.Z‖ + D := add_le_add (add_le_add h1 h2) h3
    _ = 2 * c * ‖G.Z‖ + D := by ring

theorem N_entry_bound (P c D : ℝ)
    (hadj : ∀ i j : Fin k, i.1 + 1 = j.1 →
      |G.T i j * vdot (G.col i) (G.col j)| ≤ P)
    (hbd : ∀ i : Fin k, i.1 + 1 = k → |vdot (G.col i) G.b| ≤ P)
    (hcol : ∀ l : Fin k, vnorm (G.col l) ≤ c)
    (hΔ : ∀ i j : Fin k, i.1 + 1 = j.1 → |G.T i j * (G.Δ j - G.Δ i)| ≤ D)
    (hD : 0 ≤ D) (i j : Fin k) :
    |G.N i j| ≤ max (2 * P) (2 * c * ‖G.Z‖ + D) := by
  rcases lt_trichotomy i.1 j.1 with hij | hij | hij
  · exact le_max_of_le_right (G.N_strictUpper_entry_bound c D hcol hΔ hD i j hij)
  · have heq : i = j := Fin.ext hij
    subst heq
    exact le_max_of_le_left (G.N_diag_bound P hadj hbd i)
  · rw [G.N_upper i j hij, abs_zero]
    exact le_max_of_le_left ((abs_nonneg _).trans (G.N_diag_bound P hadj hbd i))

theorem N_norm_bound (P c D : ℝ)
    (hadj : ∀ i j : Fin k, i.1 + 1 = j.1 →
      |G.T i j * vdot (G.col i) (G.col j)| ≤ P)
    (hbd : ∀ i : Fin k, i.1 + 1 = k → |vdot (G.col i) G.b| ≤ P)
    (hcol : ∀ l : Fin k, vnorm (G.col l) ≤ c)
    (hΔ : ∀ i j : Fin k, i.1 + 1 = j.1 → |G.T i j * (G.Δ j - G.Δ i)| ≤ D)
    (hD : 0 ≤ D) :
    ‖G.N‖ ≤ (k : ℝ) * max (2 * P) (2 * c * ‖G.Z‖ + D) := by
  have hentry := G.N_entry_bound P c D hadj hbd hcol hΔ hD
  exact norm_le_card_mul_of_entry_bound _ _
    ((abs_nonneg _).trans (hentry ⟨0, G.hk⟩ ⟨0, G.hk⟩)) hentry


noncomputable def pi (i : Fin k) : ℝ :=
  if h : i.1 + 1 < k then G.T i ⟨i.1 + 1, h⟩ * vdot (G.col i) (G.col ⟨i.1 + 1, h⟩)
  else vdot (G.col i) G.b

noncomputable def defectJump (i : Fin k) : ℝ :=
  if h : i.1 + 1 < k then |G.T i ⟨i.1 + 1, h⟩ * (G.Δ ⟨i.1 + 1, h⟩ - G.Δ i)| else 0

noncomputable def maxPi : ℝ := Finset.univ.sup' ⟨⟨0, G.hk⟩, Finset.mem_univ _⟩ fun i => |G.pi i|

noncomputable def maxCol : ℝ := Finset.univ.sup' ⟨⟨0, G.hk⟩, Finset.mem_univ _⟩ fun l => vnorm (G.col l)

noncomputable def maxDefectJump : ℝ := Finset.univ.sup' ⟨⟨0, G.hk⟩, Finset.mem_univ _⟩ G.defectJump

lemma defectJump_nonneg (i : Fin k) : 0 ≤ G.defectJump i := by
  unfold defectJump
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

theorem gram_commutator_bound :
    ‖G.N‖ ≤ 2 * (k : ℝ) * (G.maxPi + G.maxCol * ‖G.Z‖ + G.maxDefectJump) := by
  let i0 : Fin k := ⟨0, G.hk⟩
  have hP0 : 0 ≤ G.maxPi :=
    (abs_nonneg _).trans (Finset.le_sup' (fun i => |G.pi i|) (Finset.mem_univ i0))
  have hc0 : 0 ≤ G.maxCol :=
    (vnorm_nonneg _).trans
      (Finset.le_sup' (fun l => vnorm (G.col l)) (Finset.mem_univ i0))
  have hD0 : 0 ≤ G.maxDefectJump :=
    (G.defectJump_nonneg i0).trans (Finset.le_sup' G.defectJump (Finset.mem_univ i0))
  have hadj : ∀ i j : Fin k, i.1 + 1 = j.1 →
      |G.T i j * vdot (G.col i) (G.col j)| ≤ G.maxPi := by
    intro i j hij
    have hi : i.1 + 1 < k := hij ▸ j.2
    have hj : j = ⟨i.1 + 1, hi⟩ := Fin.ext hij.symm
    subst hj
    calc
      |G.T i ⟨i.1 + 1, hi⟩ * vdot (G.col i) (G.col ⟨i.1 + 1, hi⟩)| = |G.pi i| := by
        simp only [pi, dif_pos hi]
      _ ≤ G.maxPi := Finset.le_sup' (fun i => |G.pi i|) (Finset.mem_univ i)
  have hbd : ∀ i : Fin k, i.1 + 1 = k → |vdot (G.col i) G.b| ≤ G.maxPi := by
    intro i hi
    calc
      |vdot (G.col i) G.b| = |G.pi i| := by
        simp only [pi, dif_neg (show ¬i.1 + 1 < k by omega)]
      _ ≤ G.maxPi := Finset.le_sup' (fun i => |G.pi i|) (Finset.mem_univ i)
  have hcol : ∀ l : Fin k, vnorm (G.col l) ≤ G.maxCol := fun l =>
    Finset.le_sup' (fun l => vnorm (G.col l)) (Finset.mem_univ l)
  have hΔ : ∀ i j : Fin k, i.1 + 1 = j.1 →
      |G.T i j * (G.Δ j - G.Δ i)| ≤ G.maxDefectJump := by
    intro i j hij
    have hi : i.1 + 1 < k := hij ▸ j.2
    have hj : j = ⟨i.1 + 1, hi⟩ := Fin.ext hij.symm
    subst hj
    calc
      |G.T i ⟨i.1 + 1, hi⟩ * (G.Δ ⟨i.1 + 1, hi⟩ - G.Δ i)| = G.defectJump i := by
        simp only [defectJump, dif_pos hi]
      _ ≤ G.maxDefectJump := Finset.le_sup' G.defectJump (Finset.mem_univ i)
  have h := G.N_norm_bound G.maxPi G.maxCol G.maxDefectJump hadj hbd hcol hΔ hD0
  have hZ := norm_nonneg G.Z
  have hmax : max (2 * G.maxPi) (2 * G.maxCol * ‖G.Z‖ + G.maxDefectJump) ≤
      2 * (G.maxPi + G.maxCol * ‖G.Z‖ + G.maxDefectJump) := by
    have hcZ : 0 ≤ G.maxCol * ‖G.Z‖ := mul_nonneg hc0 hZ
    apply max_le <;> nlinarith
  calc
    ‖G.N‖ ≤ (k : ℝ) * max (2 * G.maxPi) (2 * G.maxCol * ‖G.Z‖ + G.maxDefectJump) := h
    _ ≤ (k : ℝ) * (2 * (G.maxPi + G.maxCol * ‖G.Z‖ + G.maxDefectJump)) :=
      mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)
    _ = 2 * (k : ℝ) * (G.maxPi + G.maxCol * ‖G.Z‖ + G.maxDefectJump) := by ring

end GramRecurrence
end FinitePrecisionLanczos
