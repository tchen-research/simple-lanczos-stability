import FinitePrecisionLanczos.Core.Underline


namespace FinitePrecisionLanczos

open Matrix

def tridiag (k : ℕ) (α β : ℕ → ℝ) : Mat k k := fun i j =>
  (if i = j then α (i.1 + 1) else 0)
    + (if i.1 + 1 = j.1 then β (i.1 + 1) else 0)
    + (if j.1 + 1 = i.1 then β (j.1 + 1) else 0)

lemma underlineT_tridiag_apply {k : ℕ} (α β : ℕ → ℝ) (i : Fin (k + 1)) (j : Fin k) :
    underlineT (tridiag k α β) (β k) i j =
      (if i.1 = j.1 then α (j.1 + 1) else 0) +
        (if i.1 + 1 = j.1 then β j.1 else 0) +
        (if i.1 = j.1 + 1 then β (j.1 + 1) else 0) := by
  have hj := j.isLt
  by_cases hi : i.1 < k
  · simp only [underlineT, hi, dif_pos, tridiag, Fin.ext_iff]
    generalize i.1 = a at *
    generalize j.1 = b at *
    split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring1
  · have hik : i.1 = k := by omega
    simp only [underlineT, hi, dif_neg, not_false_eq_true]
    generalize i.1 = a at *
    generalize j.1 = b at *
    subst hik
    split_ifs <;> first | (exfalso; omega) | ring1 |
      (simp only [zero_add, add_zero]; congr 1)

section Process

variable {N : Type*} [Fintype N]

structure ExactLanczosState (N : Type*) where
  prev : N → ℝ
  cur : N → ℝ
  beta : ℝ

noncomputable def exactLanczosStep (S : Matrix N N ℝ) (s : ExactLanczosState N) :
    ExactLanczosState N :=
  let a := s.cur ⬝ᵥ (S *ᵥ s.cur)
  let w := S *ᵥ s.cur - a • s.cur - s.beta • s.prev
  ⟨s.cur, (coordNorm w)⁻¹ • w, coordNorm w⟩

noncomputable def exactLanczosState (S : Matrix N N ℝ) (q : N → ℝ) :
    ℕ → ExactLanczosState N
  | 0 => ⟨0, q, 0⟩
  | j + 1 => exactLanczosStep S (exactLanczosState S q j)

noncomputable def exactLanczosVec (S : Matrix N N ℝ) (q : N → ℝ) (j : ℕ) : N → ℝ :=
  (exactLanczosState S q j).prev

noncomputable def exactLanczosBeta (S : Matrix N N ℝ) (q : N → ℝ) (j : ℕ) : ℝ :=
  (exactLanczosState S q j).beta

noncomputable def exactLanczosAlpha (S : Matrix N N ℝ) (q : N → ℝ) (j : ℕ) : ℝ :=
  exactLanczosVec S q j ⬝ᵥ (S *ᵥ exactLanczosVec S q j)

noncomputable def exactLanczosT (S : Matrix N N ℝ) (q : N → ℝ) (k : ℕ) : Mat k k :=
  tridiag k (exactLanczosAlpha S q) (exactLanczosBeta S q)

lemma exactLanczosState_succ (S : Matrix N N ℝ) (q : N → ℝ) (j : ℕ) :
    exactLanczosState S q (j + 1) = exactLanczosStep S (exactLanczosState S q j) := rfl

lemma exactLanczosVec_succ (S : Matrix N N ℝ) (q : N → ℝ) (j : ℕ) :
    exactLanczosVec S q (j + 1) = (exactLanczosState S q j).cur := rfl

end Process


section Identification

variable {N : Type*} [Fintype N] {k : ℕ} (S : Matrix N N ℝ) (u : ℕ → N → ℝ)
  (α β : ℕ → ℝ)

structure OrthonormalRecurrence (k : ℕ) : Prop where
  u_zero : u 0 = 0
  beta_zero : β 0 = 0
  orth : ∀ i j, i ≤ k → j ≤ k → u (i + 1) ⬝ᵥ u (j + 1) = if i = j then 1 else 0
  recurrence : ∀ j, j < k →
    S *ᵥ u (j + 1) = β j • u j + α (j + 1) • u (j + 1) + β (j + 1) • u (j + 2)
  beta_pos : ∀ j, 1 ≤ j → j < k → 0 < β j
  beta_last : 0 ≤ β k

namespace OrthonormalRecurrence

variable {S u α β} (h : OrthonormalRecurrence S u α β k)
include h

lemma dot_prev {j : ℕ} (hj : j ≤ k) : u (j + 1) ⬝ᵥ u j = 0 := by
  rcases j with _ | i
  · rw [h.u_zero, dotProduct_zero]
  · rw [h.orth (i + 1) i hj (by omega), if_neg (by omega)]

lemma coordNorm_eq_one {j : ℕ} (hj : j ≤ k) : coordNorm (u (j + 1)) = 1 := by
  have hsq : coordNorm (u (j + 1)) ^ 2 = 1 := by
    rw [coordNorm_sq, h.orth j j hj hj, if_pos rfl]
  nlinarith [coordNorm_nonneg (u (j + 1))]

lemma beta_nonneg {j : ℕ} (hj : j < k) : 0 ≤ β (j + 1) := by
  by_cases hjk : j + 1 < k
  · exact (h.beta_pos (j + 1) (by omega) hjk).le
  · have : j + 1 = k := by omega
    rw [this]; exact h.beta_last

lemma alpha_eq {j : ℕ} (hj : j < k) : u (j + 1) ⬝ᵥ (S *ᵥ u (j + 1)) = α (j + 1) := by
  rw [h.recurrence j hj, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
    dotProduct_smul, h.dot_prev hj.le, h.orth j j hj.le hj.le, if_pos rfl,
    h.orth j (j + 1) hj.le hj, if_neg (by omega)]
  simp

lemma residual_eq {j : ℕ} (hj : j < k) :
    S *ᵥ u (j + 1) - α (j + 1) • u (j + 1) - β j • u j = β (j + 1) • u (j + 2) := by
  rw [h.recurrence j hj]
  abel

lemma state_succ {j : ℕ} (hj : j < k)
    (hs : exactLanczosState S (u 1) j = ⟨u j, u (j + 1), β j⟩) :
    exactLanczosState S (u 1) (j + 1) =
      ⟨u (j + 1), (β (j + 1))⁻¹ • (β (j + 1) • u (j + 2)), β (j + 1)⟩ := by
  have hnorm : coordNorm (β (j + 1) • u (j + 2)) = β (j + 1) := by
    rw [coordNorm, WithLp.toLp_smul, norm_smul, ← coordNorm,
      h.coordNorm_eq_one (j := j + 1) (by omega), mul_one, Real.norm_eq_abs,
      abs_of_nonneg (h.beta_nonneg hj)]
  rw [exactLanczosState_succ, hs]
  simp only [exactLanczosStep]
  rw [h.alpha_eq hj, h.residual_eq hj, hnorm]

theorem state_eq : ∀ j, j < k → exactLanczosState S (u 1) j = ⟨u j, u (j + 1), β j⟩ := by
  intro j
  induction j with
  | zero =>
      intro _
      rw [h.u_zero, h.beta_zero]
      rfl
  | succ j ih =>
      intro hj
      rw [h.state_succ (by omega) (ih (by omega)),
        smul_smul, inv_mul_cancel₀ (h.beta_pos (j + 1) (by omega) hj).ne', one_smul]

theorem state_last (hk : 0 < k) :
    exactLanczosState S (u 1) k =
      ⟨u k, (β k)⁻¹ • (β k • u (k + 1)), β k⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact h.state_succ (by omega) (h.state_eq m (by omega))

end OrthonormalRecurrence

theorem OrthonormalRecurrence.exactLanczos {S : Matrix N N ℝ} {u : ℕ → N → ℝ}
    {α β : ℕ → ℝ} (h : OrthonormalRecurrence S u α β k) (hk : 0 < k) :
    (∀ j, j ≤ k → exactLanczosVec S (u 1) j = u j) ∧
      (∀ j, 1 ≤ j → j ≤ k → exactLanczosAlpha S (u 1) j = α j) ∧
      (∀ j, j ≤ k → exactLanczosBeta S (u 1) j = β j) ∧
      (∀ j, 1 ≤ j → j < k → 0 < exactLanczosBeta S (u 1) j) ∧
      (0 < β k → exactLanczosVec S (u 1) (k + 1) = u (k + 1)) ∧
      exactLanczosT S (u 1) k = tridiag k α β := by
  have hstate : ∀ j, j ≤ k → (exactLanczosState S (u 1) j).prev = u j ∧
      (exactLanczosState S (u 1) j).beta = β j := by
    intro j hj
    rcases Nat.lt_or_ge j k with hjk | hjk
    · rw [h.state_eq j hjk]; exact ⟨rfl, rfl⟩
    · have : j = k := by omega
      subst this
      rw [h.state_last hk]; exact ⟨rfl, rfl⟩
  have hvec : ∀ j, j ≤ k → exactLanczosVec S (u 1) j = u j := fun j hj => (hstate j hj).1
  have hbeta : ∀ j, j ≤ k → exactLanczosBeta S (u 1) j = β j := fun j hj => (hstate j hj).2
  have halpha : ∀ j, 1 ≤ j → j ≤ k → exactLanczosAlpha S (u 1) j = α j := by
    intro j h1 h2
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    rw [exactLanczosAlpha, hvec (m + 1) h2, h.alpha_eq (by omega)]
  refine ⟨hvec, halpha, hbeta, ?_, ?_, ?_⟩
  · intro j h1 h2
    rw [hbeta j h2.le]; exact h.beta_pos j h1 h2
  · intro hpos
    rw [exactLanczosVec_succ, h.state_last hk]
    change (β k)⁻¹ • (β k • u (k + 1)) = u (k + 1)
    rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  · ext i j
    simp only [exactLanczosT, tridiag]
    rw [halpha (i.1 + 1) (by omega) i.isLt, hbeta (i.1 + 1) i.isLt,
      hbeta (j.1 + 1) j.isLt]

end Identification


section MatrixForm

variable {N : Type*} {k : ℕ}

def colSeq (W : Matrix N (Fin (k + 1)) ℝ) (j : ℕ) : N → ℝ :=
  fun a => if h : 1 ≤ j ∧ j ≤ k + 1 then W a ⟨j - 1, by omega⟩ else 0

lemma colSeq_succ (W : Matrix N (Fin (k + 1)) ℝ) {j : ℕ} (hj : j ≤ k) :
    colSeq W (j + 1) = fun a => W a ⟨j, by omega⟩ := by
  funext a
  rw [colSeq, dif_pos (by omega)]
  rfl

lemma colSeq_zero (W : Matrix N (Fin (k + 1)) ℝ) : colSeq W 0 = 0 := by
  funext a
  simp [colSeq]

lemma sum_mul_ite_val [Fintype N] (W : Matrix N (Fin (k + 1)) ℝ) (a : N) (m : ℕ) (hm : m < k + 1)
    (c : ℝ) :
    ∑ i : Fin (k + 1), W a i * (if i.1 = m then c else 0) = W a ⟨m, hm⟩ * c := by
  rw [Finset.sum_eq_single ⟨m, hm⟩]
  · simp
  · intro b _ hb
    have : b.1 ≠ m := fun h => hb (Fin.ext h)
    simp [this]
  · simp

theorem orthonormalRecurrence_of_matrix [Fintype N] (S : Matrix N N ℝ)
    (W : Matrix N (Fin (k + 1)) ℝ) (α β : ℕ → ℝ) (hβ0 : β 0 = 0)
    (hpos : ∀ j, 1 ≤ j → j < k → 0 < β j) (hβk : 0 ≤ β k)
    (hW : Wᵀ * W = 1)
    (hrec : S * leadCols W = W * underlineT (tridiag k α β) (β k)) :
    OrthonormalRecurrence S (colSeq W) α β k where
  u_zero := colSeq_zero W
  beta_zero := hβ0
  orth i j hi hj := by
    rw [colSeq_succ W hi, colSeq_succ W hj]
    have h := congrFun (congrFun hW ⟨i, by omega⟩) ⟨j, by omega⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [Matrix.transpose_apply, Fin.mk.injEq] at h
    rw [dotProduct, h]
  recurrence j hj := by
    funext a
    have h := congrFun (congrFun hrec a) ⟨j, hj⟩
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    simp only [underlineT_tridiag_apply, mul_add, Finset.sum_add_distrib] at h
    rw [sum_mul_ite_val W a j (by omega), sum_mul_ite_val W a (j + 1) (by omega)] at h
    rw [colSeq_succ W hj.le, colSeq_succ W (show j + 1 ≤ k by omega)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    have hleft : ∑ x, S a x * W x ⟨j, by omega⟩ = ∑ x, S a x * leadCols W x ⟨j, hj⟩ := rfl
    rw [hleft, h]
    rcases j with _ | m
    · have hz : ∀ i : Fin (k + 1), W a i * (if i.1 + 1 = 0 then β 0 else 0) = 0 := by
        intro i; simp
      rw [Finset.sum_congr rfl (fun i _ => hz i), colSeq_zero]
      simp; ring
    · have hmid : ∑ i : Fin (k + 1), W a i * (if i.1 + 1 = m + 1 then β (m + 1) else 0) =
          W a ⟨m, by omega⟩ * β (m + 1) := by
        rw [← sum_mul_ite_val W a m (by omega)]
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        by_cases him : i.1 = m
        · rw [if_pos (by omega), if_pos him]
        · rw [if_neg (by omega), if_neg him]
      rw [hmid, colSeq_succ W (show m ≤ k by omega)]
      ring
  beta_pos := hpos
  beta_last := hβk

end MatrixForm

end FinitePrecisionLanczos
