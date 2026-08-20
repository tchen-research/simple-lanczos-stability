import FinitePrecisionLanczos.Lanczos.Greenbaum.Model
























namespace FinitePrecisionLanczos

open Matrix






structure ExactLanczos {N : Type*} [Fintype N] [DecidableEq N]
    (S : Matrix N N ℝ) (q : N → ℝ) (steps : ℕ) where
  v : ℕ → N → ℝ
  α : ℕ → ℝ
  β : ℕ → ℝ
  hv_zero : v 0 = 0
  hβ_zero : β 0 = 0
  hfirst : v 1 = q
  hunit : ∀ j, j < steps → v (j + 1) ⬝ᵥ v (j + 1) = 1
  hα : ∀ j, j < steps → α (j + 1) = v (j + 1) ⬝ᵥ S.mulVec (v (j + 1))
  hβ_pos : ∀ j, j + 1 < steps → 0 < β (j + 1)
  hrec : ∀ j, j + 1 < steps →
    β (j + 1) • v (j + 2) =
      S.mulVec (v (j + 1)) - α (j + 1) • v (j + 1) - β j • v j


lemma mulVec_single_column {N : Type*} [Fintype N] [DecidableEq N]
    (A : Matrix N N ℝ) (a : N) :
    A.mulVec (Pi.single a 1) = fun i => A i a := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

namespace ExactLanczos

variable {N : Type*} [Fintype N] [DecidableEq N]
  {S : Matrix N N ℝ} {q : N → ℝ} {steps : ℕ}

lemma eq_of_sq_eq_sq_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  have hfac : (a - b) * (a + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · linarith
  · linarith


lemma beta_sq (R : ExactLanczos S q steps) {j : ℕ} (hj : j + 1 < steps) :
    R.β (j + 1) ^ 2 =
      (S.mulVec (R.v (j + 1)) - R.α (j + 1) • R.v (j + 1) - R.β j • R.v j) ⬝ᵥ
      (S.mulVec (R.v (j + 1)) - R.α (j + 1) • R.v (j + 1) - R.β j • R.v j) := by
  have hu : R.v (j + 2) ⬝ᵥ R.v (j + 2) = 1 := R.hunit (j + 1) hj
  rw [← R.hrec j hj, smul_dotProduct, dotProduct_smul, hu]
  simp [smul_eq_mul, pow_two]




theorem run_unique (R R' : ExactLanczos S q steps) :
    ∀ j, j < steps →
      R.v (j + 1) = R'.v (j + 1) ∧ R.v j = R'.v j ∧ R.β j = R'.β j := by
  intro j
  induction j with
  | zero =>
      intro _
      exact ⟨R.hfirst.trans R'.hfirst.symm,
        R.hv_zero.trans R'.hv_zero.symm,
        R.hβ_zero.trans R'.hβ_zero.symm⟩
  | succ m ih =>
      intro h
      have hm : m < steps := Nat.lt_of_succ_lt h
      obtain ⟨hv1, hv0, hb0⟩ := ih hm
      have hal : R.α (m + 1) = R'.α (m + 1) := by
        rw [R.hα m hm, R'.hα m hm, hv1]
      have hw : S.mulVec (R.v (m + 1)) - R.α (m + 1) • R.v (m + 1)
            - R.β m • R.v m
          = S.mulVec (R'.v (m + 1)) - R'.α (m + 1) • R'.v (m + 1)
            - R'.β m • R'.v m := by
        rw [hv1, hv0, hb0, hal]
      have hb1 := R.hβ_pos m h
      have hb2 := R'.hβ_pos m h
      have hsq : R.β (m + 1) ^ 2 = R'.β (m + 1) ^ 2 := by
        rw [R.beta_sq h, R'.beta_sq h, hw]
      have hβ : R.β (m + 1) = R'.β (m + 1) :=
        eq_of_sq_eq_sq_of_pos hb1 hb2 hsq
      have hv2 : R.v (m + 2) = R'.v (m + 2) := by
        have hchain : R.β (m + 1) • R.v (m + 2)
            = R.β (m + 1) • R'.v (m + 2) := by
          rw [R.hrec m h, hβ, R'.hrec m h, hw]
        exact smul_right_injective (N → ℝ) (ne_of_gt hb1) hchain
      exact ⟨hv2, hv1, hβ⟩


theorem alpha_unique (R R' : ExactLanczos S q steps) {j : ℕ}
    (hj : j < steps) : R.α (j + 1) = R'.α (j + 1) := by
  rw [R.hα j hj, R'.hα j hj, (run_unique R R' j hj).1]


theorem beta_unique (R R' : ExactLanczos S q steps) {j : ℕ}
    (hj : j + 1 < steps) : R.β (j + 1) = R'.β (j + 1) :=
  (run_unique R R' (j + 1) hj).2.2



def T (R : ExactLanczos S q steps) : Matrix (Fin steps) (Fin steps) ℝ :=
  fun i j =>
    (if i = j then R.α (i.1 + 1) else 0)
      + (if i.1 + 1 = j.1 then R.β (i.1 + 1) else 0)
      + (if j.1 + 1 = i.1 then R.β (j.1 + 1) else 0)

end ExactLanczos

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

namespace GreenbaumModel

variable (M : L.GreenbaumModel)



def lanczosBasis (j : ℕ) : Fin k ⊕ Fin M.d → ℝ :=
  if h : 1 ≤ j ∧ j ≤ k
    then Pi.single (Sum.inl (⟨j - 1, by omega⟩ : Fin k)) 1 else 0

lemma lanczosBasis_of_le (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ k) :
    lanczosBasis L M j =
      Pi.single (Sum.inl (⟨j - 1, by omega⟩ : Fin k)) 1 :=
  dif_pos ⟨h1, h2⟩

lemma lanczosBasis_zero : lanczosBasis L M 0 = 0 :=
  dif_neg (by omega)



lemma lanczosBasis_apply_inl (m : ℕ) (hm : m ≤ k) (a : Fin k) :
    lanczosBasis L M m (Sum.inl a) = if a.1 + 1 = m then 1 else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · rw [lanczosBasis_zero]
    simp
  · rw [lanczosBasis_of_le L M m hpos hm]
    rcases eq_or_ne (a.1 + 1) m with h | h
    · rw [if_pos h]
      have ha : (Sum.inl (⟨m - 1, by omega⟩ : Fin k) : Fin k ⊕ Fin M.d)
          = Sum.inl a :=
        congrArg Sum.inl (Fin.ext (show m - 1 = a.1 by omega))
      rw [ha, Pi.single_eq_same]
    · rw [if_neg h]
      refine Pi.single_eq_of_ne (fun hcon => ?_) 1
      have hval : a.1 = m - 1 := congrArg Fin.val (Sum.inl.inj hcon)
      omega


lemma lanczosBasis_apply_inr (m : ℕ) (r : Fin M.d) :
    lanczosBasis L M m (Sum.inr r) = 0 := by
  unfold lanczosBasis
  split
  · exact Pi.single_eq_of_ne (by simp) 1
  · rfl



lemma Ttilde_tail_zero {j : Fin k} (hj : j.1 + 1 < k) (r : Fin M.d) :
    M.Ttilde (Sum.inr r) (Sum.inl j) = 0 := by
  have htri := M.Ttilde_tridiagonal (Sum.inl j) (Sum.inr r)
    (by simp only [sumPosition]; omega)
  calc M.Ttilde (Sum.inr r) (Sum.inl j)
      = Matrix.transpose M.Ttilde (Sum.inl j) (Sum.inr r) := rfl
    _ = M.Ttilde (Sum.inl j) (Sum.inr r) := by rw [M.Ttilde_symmetric]
    _ = 0 := htri





noncomputable def exactLanczosRun :
    ExactLanczos M.Ttilde (completionFirst L.hk_pos M.d) k where
  v := lanczosBasis L M
  α := L.α
  β := L.β
  hv_zero := lanczosBasis_zero L M
  hβ_zero := L.hβ_zero
  hfirst := by
    rw [lanczosBasis_of_le L M 1 le_rfl L.hk_pos]
    rfl
  hunit := by
    intro j hj
    rw [lanczosBasis_of_le L M (j + 1) (by omega) (by omega)]
    simp [single_dotProduct]
  hα := by
    intro j hj
    rw [lanczosBasis_of_le L M (j + 1) (by omega) (by omega),
      mulVec_single_column]
    have e1 : ¬(j + 1 = j) := by omega
    simp [single_dotProduct, M.leading_block, Tmat,
      Nat.add_sub_cancel, e1]
  hβ_pos := by
    intro j hj
    exact L.hβ_internal (j + 1) (by omega) (by omega)
  hrec := by
    intro j hj
    have hexp : M.Ttilde.mulVec (lanczosBasis L M (j + 1)) =
        fun i => M.Ttilde i (Sum.inl (⟨j, by omega⟩ : Fin k)) := by
      rw [lanczosBasis_of_le L M (j + 1) (by omega) (by omega)]
      exact mulVec_single_column _ _
    funext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hexp]
    rcases i with a | r
    ·
      rw [M.leading_block a _,
        lanczosBasis_apply_inl L M (j + 2) (by omega) a,
        lanczosBasis_apply_inl L M (j + 1) (by omega) a,
        lanczosBasis_apply_inl L M j (by omega) a]
      simp only [Tmat, Fin.ext_iff, Nat.add_sub_cancel]
      split_ifs <;> simp_all <;> omega
    ·
      have htail : M.Ttilde (Sum.inr r)
          (Sum.inl (⟨j, by omega⟩ : Fin k)) = 0 :=
        Ttilde_tail_zero L M (show j + 1 < k from hj) r
      simp [lanczosBasis_apply_inr, htail]


theorem exact_lanczos_alpha
    (R : ExactLanczos M.Ttilde (completionFirst L.hk_pos M.d) k)
    {j : ℕ} (hj : j < k) : R.α (j + 1) = L.α (j + 1) :=
  ExactLanczos.alpha_unique R (exactLanczosRun L M) hj


theorem exact_lanczos_beta
    (R : ExactLanczos M.Ttilde (completionFirst L.hk_pos M.d) k)
    {j : ℕ} (hj : j + 1 < k) : R.β (j + 1) = L.β (j + 1) :=
  ExactLanczos.beta_unique R (exactLanczosRun L M) hj



theorem exact_lanczos_returns_Tmat
    (R : ExactLanczos M.Ttilde (completionFirst L.hk_pos M.d) k) :
    R.T = L.Tmat := by
  ext i j
  simp only [ExactLanczos.T, Tmat]
  have e1 : (if i = j then R.α (i.1 + 1) else 0)
      = (if i = j then L.α (i.1 + 1) else 0) := by
    by_cases h : i = j
    · simp only [if_pos h]
      exact exact_lanczos_alpha L M R i.isLt
    · simp only [if_neg h]
  have e2 : (if i.1 + 1 = j.1 then R.β (i.1 + 1) else 0)
      = (if i.1 + 1 = j.1 then L.β (i.1 + 1) else 0) := by
    by_cases h : i.1 + 1 = j.1
    · simp only [if_pos h]
      exact exact_lanczos_beta L M R (by have := j.isLt; omega)
    · simp only [if_neg h]
  have e3 : (if j.1 + 1 = i.1 then R.β (j.1 + 1) else 0)
      = (if j.1 + 1 = i.1 then L.β (j.1 + 1) else 0) := by
    by_cases h : j.1 + 1 = i.1
    · simp only [if_pos h]
      exact exact_lanczos_beta L M R (by have := i.isLt; omega)
    · simp only [if_neg h]
  rw [e1, e2, e3]

end GreenbaumModel
end LanczosRun
end FinitePrecisionLanczos
