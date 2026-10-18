import FinitePrecisionLanczos.Lanczos.Normalized.LocalErrors
import FinitePrecisionLanczos.Lanczos.ComputedCommutator

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

noncomputable def normalizedSaad : SaadGramRecurrence n k where
  hk := L.hk_pos
  A := L.H
  T := L.Tmat
  β := L.β k
  W := L.normalizedVsucc
  Z := L.normalizedFmat
  Y := L.normalizedR
  Γ := fun _ => 0
  hA := L.hHsymm
  hT := L.Tmat_transpose
  htri := L.Tmat_tridiagonal
  hrec := by rw [leadCols_normalizedVsucc]; exact L.normalized_governing_succ
  hY := L.normalizedR_strictUpper
  hgram := by
    rw [leadCols_normalizedVsucc, L.normalized_gram_split, Matrix.diagonal_zero, add_zero]

noncomputable def normalizedCommutator : Mat k k :=
  L.Tmat * L.normalizedR - L.normalizedR * L.Tmat -
    L.β k • lastOuter L.hk_pos (L.normalizedVᵀ *ᵥ L.normalizedVNext)

lemma normalizedSaad_N : L.normalizedSaad.N = L.normalizedCommutator := by
  simp only [SaadGramRecurrence.N, normalizedCommutator, normalizedSaad,
    leadCols_normalizedVsucc, lastCol_normalizedVsucc]


theorem normalizedCommutator_upper : Upper L.normalizedCommutator :=
  L.normalizedSaad_N ▸ L.normalizedSaad.N_upper

theorem normalized_commutator_skew :
    L.normalizedCommutator - L.normalizedCommutatorᵀ =
      L.normalizedVᵀ * L.normalizedFmat - L.normalizedFmatᵀ * L.normalizedV := by
  have h := L.normalizedSaad.N_skew
  rw [normalizedSaad_N] at h
  rw [h]
  simp [normalizedSaad]


lemma normalizedSaad_col (l : Fin (k + 1)) :
    L.normalizedSaad.col l = L.normalizedVec (l.1 + 1) := rfl

lemma normalizedSaad_pi (i : Fin k) : L.normalizedSaad.pi i = L.normalizedP (i.1 + 1) := by
  simp only [SaadGramRecurrence.pi, normalizedSaad_col]
  change L.underlineTmat i.succ i * _ = _
  rw [L.underlineTmat_succ_self]
  simp [normalizedP, vdot, dotProduct_smul, smul_eq_mul]

lemma normalized_product (i : Fin k) :
    |L.normalizedSaad.pi i| ≤ (4800 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  rw [L.normalizedSaad_pi]
  exact L.normalizedP_bound (by omega) (by omega)

theorem normalizedCommutator_bound :
    ‖L.normalizedCommutator‖ ≤ (9600 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by
  have hs : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have h := L.normalizedSaad.N_norm_bound ((4800 * (k : ℝ)) * L.ε * ‖L.H‖) 1 0
    L.normalized_product
    (fun l => by rw [L.normalizedSaad_col]; exact
      (L.normalizedVec_unit (by omega) (by simp)).le)
    (fun i j _ => by simp [normalizedSaad]) le_rfl
  have hF : ‖L.normalizedSaad.Z‖ ≤ (1500 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖ :=
    L.normalizedFmat_bound
  have hmax : max (2 * ((4800 * (k : ℝ)) * L.ε * ‖L.H‖))
      (2 * 1 * ‖L.normalizedSaad.Z‖ + 0) ≤
        (9600 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖ := by
    apply max_le
    · have : (9600 * (k : ℝ)) * (L.ε * ‖L.H‖) ≤
          (9600 * (k : ℝ) ^ 2) * (L.ε * ‖L.H‖) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hs
      linarith
    · have : (3000 * (k : ℝ) ^ 2) * (L.ε * ‖L.H‖) ≤
          (9600 * (k : ℝ) ^ 2) * (L.ε * ‖L.H‖) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hs
      linarith
  rw [← L.normalizedSaad_N]
  calc
    ‖L.normalizedSaad.N‖ ≤ (k : ℝ) * max (2 * ((4800 * (k : ℝ)) * L.ε * ‖L.H‖))
        (2 * 1 * ‖L.normalizedSaad.Z‖ + 0) := h
    _ ≤ (k : ℝ) * ((9600 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖) :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = (9600 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by ring

structure NormalizedGramCommutator : Prop where
  upper : Upper L.normalizedCommutator
  skew_identity :
    L.normalizedCommutator - L.normalizedCommutatorᵀ =
      L.normalizedVᵀ * L.normalizedFmat - L.normalizedFmatᵀ * L.normalizedV
  norm_bound : ‖L.normalizedCommutator‖ ≤
    (9600 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖

theorem normalized_gram_commutator : L.NormalizedGramCommutator where
  upper := L.normalizedCommutator_upper
  skew_identity := L.normalized_commutator_skew
  norm_bound := L.normalizedCommutator_bound

end LanczosRun
end FinitePrecisionLanczos
