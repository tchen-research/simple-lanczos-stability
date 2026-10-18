import FinitePrecisionLanczos.Lanczos.Ritz
import FinitePrecisionLanczos.Core.SaadGramCommutator

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

theorem Tmat_tridiagonal : Tridiagonal L.Tmat := by
  intro i j h
  have h1 : i ≠ j := by rintro rfl; omega
  have h2 : ¬i.1 + 1 = j.1 := by omega
  have h3 : ¬j.1 + 1 = i.1 := by omega
  simp [Tmat, h1, h2, h3]

def computedR : Mat k k := fun i j =>
  if i.1 < j.1 then (L.Vmatᵀ * L.Vmat) i j else 0

lemma computedR_strictUpper : StrictUpper L.computedR := by
  intro i j hij
  simp [computedR, hij]

lemma computedGram_diag (j : Fin k) :
    (L.Vmatᵀ * L.Vmat) j j = 1 + L.g (j.1 + 1) := by
  simp [Matrix.mul_apply, Vmat, ofCols, g, vdot, dotProduct]

theorem computed_gram_split :
    L.Vmatᵀ * L.Vmat =
      1 + L.computedRᵀ + Matrix.diagonal (fun j => L.g (j.1 + 1)) + L.computedR := by
  ext i j
  rcases lt_trichotomy i.1 j.1 with hij | hij | hij
  · have hne : i ≠ j := by intro h; subst j; omega
    simp [computedR, hij, not_lt_of_ge hij.le, hne]
  · have heq : i = j := Fin.ext hij
    subst j
    simp [computedR, L.computedGram_diag]
  · have hne : i ≠ j := by intro h; subst j; omega
    have hsym : (L.Vmatᵀ * L.Vmat) j i = (L.Vmatᵀ * L.Vmat) i j := by
      simp [Matrix.mul_apply]
      exact dotProduct_comm _ _
    simp [computedR, hij, not_lt_of_ge hij.le, hne, hsym]

def computedSaad : SaadGramRecurrence n k where
  hk := L.hk_pos
  A := L.H
  T := L.Tmat
  β := L.β k
  W := L.Vsucc
  Z := L.Fmat
  Y := L.computedR
  Γ := fun j => L.g (j.1 + 1)
  hA := L.hHsymm
  hT := L.Tmat_transpose
  htri := L.Tmat_tridiagonal
  hrec := L.governing
  hY := L.computedR_strictUpper
  hgram := L.computed_gram_split

noncomputable def computedCommutator : Mat k k :=
  L.Tmat * L.computedR - L.computedR * L.Tmat -
    L.β k • lastOuter L.hk_pos (L.Vmatᵀ *ᵥ L.v (k + 1))

lemma computedSaad_N : L.computedSaad.N = L.computedCommutator := rfl

theorem computedCommutator_eq_rawBoundary :
    L.computedCommutator =
      L.Tmat * L.computedR - L.computedR * L.Tmat -
        lastOuter L.hk_pos (L.Vmatᵀ *ᵥ L.rawBoundary) := by
  rw [computedCommutator, rawBoundary, Matrix.mulVec_smul, lastOuter_smul]

theorem computedCommutator_upper : Upper L.computedCommutator :=
  L.computedSaad.N_upper

theorem computed_commutator_skew :
    L.computedCommutator - L.computedCommutatorᵀ =
      L.Vmatᵀ * L.Fmat - L.Fmatᵀ * L.Vmat -
        (L.Tmat * Matrix.diagonal (fun j => L.g (j.1 + 1)) -
          Matrix.diagonal (fun j => L.g (j.1 + 1)) * L.Tmat) :=
  L.computedSaad.N_skew


lemma Tmat_superdiag (i j : Fin k) (hij : i.1 + 1 = j.1) :
    L.Tmat i j = L.β (i.1 + 1) := by
  have hne : i ≠ j := by rintro rfl; omega
  have h3 : ¬j.1 + 1 = i.1 := by omega
  simp [Tmat, hne, hij, h3]

lemma underlineTmat_succ_self (i : Fin k) :
    L.underlineTmat i.succ i = L.β (i.1 + 1) := by
  rw [underlineTmat, underlineT_succ_self]
  split_ifs with h
  · rw [← L.Tmat_transpose, Matrix.transpose_apply]
    exact L.Tmat_superdiag i _ rfl
  · congr 1
    omega

lemma computedSaad_col (l : Fin (k + 1)) : L.computedSaad.col l = L.v (l.1 + 1) := rfl

lemma computedSaad_pi (i : Fin k) : L.computedSaad.pi i = L.p (i.1 + 1) := by
  simp only [SaadGramRecurrence.pi, computedSaad_col]
  change L.underlineTmat i.succ i * _ = _
  rw [L.underlineTmat_succ_self]
  simp [p, vdot, dotProduct_smul, smul_eq_mul]

lemma computed_product (i : Fin k) :
    |L.computedSaad.pi i| ≤ (1200 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  rw [L.computedSaad_pi]
  have hb := L.local_product_bound (i.1 + 1) (by omega) (by omega)
  have hik : ((i.1 + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast (show i.1 + 1 ≤ k by omega)
  have hs : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
  nlinarith

lemma computed_col_bound (l : Fin k) : vnorm (L.computedSaad.col l.castSucc) ≤ 2 :=
  L.vnorm_v_le_two (by omega) (Nat.succ_le_iff.mpr l.2)

lemma computed_defect_difference (i j : Fin k) (hij : i.1 + 1 = j.1) :
    |L.computedSaad.T i j * (L.computedSaad.Γ j - L.computedSaad.Γ i)| ≤
      (8 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  change |L.Tmat i j * (L.g (j.1 + 1) - L.g (i.1 + 1))| ≤ _
  rw [L.Tmat_superdiag i j hij, abs_mul,
    abs_of_nonneg (L.hβ_nonneg _ (by omega))]
  have hgj := L.abs_g_le (j.1 + 1) (by omega) (Nat.succ_le_iff.mpr j.2)
  have hgi := L.abs_g_le (i.1 + 1) (by omega) (Nat.succ_le_iff.mpr i.2)
  have hdiff : |L.g (j.1 + 1) - L.g (i.1 + 1)| ≤ 2 * L.ε :=
    (abs_sub _ _).trans (by linarith)
  have hb := L.beta_bound (i.1 + 1) (by omega)
  have hb0 := L.hβ_nonneg (i.1 + 1) (by omega)
  have hik : ((i.1 + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast (show i.1 + 1 ≤ k by omega)
  have hbk : L.β (i.1 + 1) ≤ (4 * (k : ℝ)) * ‖L.H‖ :=
    hb.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  calc
    L.β (i.1 + 1) * |L.g (j.1 + 1) - L.g (i.1 + 1)| ≤
        ((4 * (k : ℝ)) * ‖L.H‖) * (2 * L.ε) :=
      mul_le_mul hbk hdiff (abs_nonneg _) (by positivity)
    _ = (8 * (k : ℝ)) * L.ε * ‖L.H‖ := by ring

theorem computedCommutator_bound :
    ‖L.computedCommutator‖ ≤ (3000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by
  have hs : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have h := L.computedSaad.N_norm_bound ((1200 * (k : ℝ)) * L.ε * ‖L.H‖) 2
    ((8 * (k : ℝ)) * L.ε * ‖L.H‖) L.computed_product L.computed_col_bound
    L.computed_defect_difference (by have := L.hε_nonneg; positivity)
  have hF : ‖L.computedSaad.Z‖ ≤ (700 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖ := L.Fmat_bound
  have hmax : max (2 * ((1200 * (k : ℝ)) * L.ε * ‖L.H‖))
      (2 * 2 * ‖L.computedSaad.Z‖ + (8 * (k : ℝ)) * L.ε * ‖L.H‖) ≤
        (3000 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖ := by
    apply max_le
    · have : (2400 * (k : ℝ)) * (L.ε * ‖L.H‖) ≤ (3000 * (k : ℝ) ^ 2) * (L.ε * ‖L.H‖) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hs
      linarith
    · have : (2808 * (k : ℝ) ^ 2) * (L.ε * ‖L.H‖) ≤ (3000 * (k : ℝ) ^ 2) * (L.ε * ‖L.H‖) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hs
      have h8 : (8 * (k : ℝ)) * (L.ε * ‖L.H‖) ≤ (8 * (k : ℝ) ^ 2) * (L.ε * ‖L.H‖) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hs
      nlinarith
  rw [← L.computedSaad_N]
  calc
    ‖L.computedSaad.N‖ ≤ (k : ℝ) * max (2 * ((1200 * (k : ℝ)) * L.ε * ‖L.H‖))
        (2 * 2 * ‖L.computedSaad.Z‖ + (8 * (k : ℝ)) * L.ε * ‖L.H‖) := h
    _ ≤ (k : ℝ) * ((3000 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖) :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = (3000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by ring

structure ComputedGramCommutator : Prop where
  upper : Upper L.computedCommutator
  skew_identity :
    L.computedCommutator - L.computedCommutatorᵀ =
      L.Vmatᵀ * L.Fmat - L.Fmatᵀ * L.Vmat -
        (L.Tmat * Matrix.diagonal (fun j => L.g (j.1 + 1)) -
          Matrix.diagonal (fun j => L.g (j.1 + 1)) * L.Tmat)
  norm_bound : ‖L.computedCommutator‖ ≤ (3000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖

theorem computed_gram_commutator : L.ComputedGramCommutator where
  upper := L.computedCommutator_upper
  skew_identity := L.computed_commutator_skew
  norm_bound := L.computedCommutator_bound

end LanczosRun
end FinitePrecisionLanczos
