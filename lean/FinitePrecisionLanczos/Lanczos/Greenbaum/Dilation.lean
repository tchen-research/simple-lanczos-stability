import FinitePrecisionLanczos.Lanczos.Normalized.Commutator
import FinitePrecisionLanczos.Core.DilationSaad


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)


noncomputable def normalizedRsucc : Mat (k + 1) (k + 1) :=
  strictUpperPart (L.normalizedVsuccᵀ * L.normalizedVsucc)

lemma normalizedRsucc_strictUpper : StrictUpper L.normalizedRsucc :=
  strictUpperPart_strictUpper _

theorem normalized_gram_split_succ :
    L.normalizedVsuccᵀ * L.normalizedVsucc =
      1 + L.normalizedRsuccᵀ + L.normalizedRsucc := by
  have h := eq_one_add_strictUpperPart (L.normalizedVsuccᵀ * L.normalizedVsucc)
    (by rw [Matrix.transpose_mul, Matrix.transpose_transpose])
    (fun j => by
      have hsq := vnorm_sq (fun i => L.normalizedVsucc i j)
      rw [L.normalizedVsucc_unit] at hsq
      simpa [Matrix.mul_apply, vdot, dotProduct] using hsq.symm)
  rw [h, normalizedRsucc]
  abel

lemma leadBlock_normalizedRsucc : leadBlock L.normalizedRsucc = L.normalizedR := by
  rw [normalizedRsucc, leadBlock_strictUpperPart_gram, leadCols_normalizedVsucc]
  rfl

theorem normalizedRsucc_block :
    leadBlock L.normalizedRsucc = L.normalizedR ∧
      (∀ i : Fin k, L.normalizedRsucc i.castSucc (Fin.last k) =
        (L.normalizedVᵀ *ᵥ L.normalizedVNext) i) ∧
      (∀ j, L.normalizedRsucc (Fin.last k) j = 0) := by
  refine ⟨L.leadBlock_normalizedRsucc, fun i => ?_, strictUpperPart_last _⟩
  rw [normalizedRsucc, strictUpperPart_gram_castSucc_last, leadCols_normalizedVsucc,
    lastCol_normalizedVsucc]


noncomputable def greenbaumCsucc : Mat (k + 1) (k + 1) := triangularC L.normalizedRsucc

noncomputable def greenbaumKsucc : Mat (k + 1) (k + 1) := triangularK L.normalizedRsucc

noncomputable def greenbaumC : Mat k k := triangularC L.normalizedR

noncomputable def greenbaumK : Mat k k := triangularK L.normalizedR

noncomputable def greenbaumL : Mat k k :=
  L.greenbaumC * L.normalizedCommutator * L.greenbaumC

noncomputable def greenbaumD (r : ℕ) : Mat k k :=
  powerResidual L.greenbaumK L.greenbaumL r

theorem greenbaum_CK_blocks :
    leadBlock L.greenbaumCsucc = L.greenbaumC ∧
      leadBlock L.greenbaumKsucc = L.greenbaumK ∧
      L.greenbaumKsucc = L.normalizedRsucc * L.greenbaumCsucc ∧
      L.greenbaumK = L.normalizedR * L.greenbaumC := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [greenbaumCsucc, leadBlock_triangularC L.hk_pos _ L.normalizedRsucc_strictUpper,
      L.leadBlock_normalizedRsucc]
    rfl
  · rw [greenbaumKsucc, leadBlock_triangularK L.hk_pos _ L.normalizedRsucc_strictUpper,
      L.leadBlock_normalizedRsucc]
    rfl
  · exact triangularK_eq_mul (Nat.succ_pos k) _ L.normalizedRsucc_strictUpper
  · exact triangularK_eq_mul L.hk_pos _ L.normalizedR_strictUpper


def greenbaumBlockOperator :
    Matrix (Fin (k + 1) × Fin n) (Fin (k + 1) × Fin n) ℝ := blockDiagonal L.H

noncomputable def greenbaumVhat : Matrix (Fin (k + 1) × Fin n) (Fin (k + 1)) ℝ :=
  dilationStack (k + 1) L.normalizedVsucc L.greenbaumCsucc L.greenbaumKsucc

noncomputable def greenbaumX : Matrix (Fin (k + 1) × Fin n) (Fin k) ℝ :=
  leadCols L.greenbaumVhat

noncomputable def greenbaumVNext : (Fin (k + 1) × Fin n) → ℝ :=
  lastCol L.greenbaumVhat

noncomputable def greenbaumVhatBlock (r : ℕ) : Mat n (k + 1) :=
  L.normalizedVsucc * L.greenbaumCsucc * L.greenbaumKsucc ^ r

noncomputable def greenbaumVBlock (r : ℕ) : Mat n k :=
  L.normalizedV * L.greenbaumC * L.greenbaumK ^ r

noncomputable def greenbaumError : Matrix (Fin (k + 1) × Fin n) (Fin k) ℝ :=
  physicalError L.normalizedV L.normalizedFmat L.greenbaumC L.greenbaumK L.greenbaumD

noncomputable def greenbaumErrorBlock (r : ℕ) : Mat n k :=
  physicalErrorBlock L.normalizedV L.normalizedFmat L.greenbaumC
    L.greenbaumK L.greenbaumD r

theorem leadCols_greenbaumVhatBlock (r : ℕ) :
    leadCols (L.greenbaumVhatBlock r) = L.greenbaumVBlock r :=
  saad_leadCols_block L.hk_pos L.normalizedVsucc L.normalizedV L.normalizedRsucc
    L.normalizedR L.normalizedRsucc_strictUpper L.leadBlock_normalizedRsucc
    L.leadCols_normalizedVsucc r


theorem greenbaum_isometry_identity :
    L.greenbaumCsuccᵀ * (L.normalizedVsuccᵀ * L.normalizedVsucc) * L.greenbaumCsucc =
      1 - L.greenbaumKsuccᵀ * L.greenbaumKsucc :=
  triangular_isometry_identity (Nat.succ_pos k) _ L.normalizedRsucc
    L.normalizedRsucc_strictUpper (by rw [L.normalized_gram_split_succ]; abel)

lemma greenbaumKsucc_nilpotent : L.greenbaumKsucc ^ (k + 1) = 0 :=
  triangularK_pow_card_eq_zero (Nat.succ_pos k) _ L.normalizedRsucc_strictUpper

theorem greenbaum_Kkp_power :
    L.greenbaumKsucc ^ (k + 1) = 0 ∧
      L.greenbaumCsucc *ᵥ firstCoord (Nat.succ_pos k) = firstCoord (Nat.succ_pos k) ∧
      L.greenbaumKsucc *ᵥ firstCoord (Nat.succ_pos k) = 0 :=
  ⟨L.greenbaumKsucc_nilpotent,
    triangularC_first (Nat.succ_pos k) _ L.normalizedRsucc_strictUpper,
    triangularK_first (Nat.succ_pos k) _ L.normalizedRsucc_strictUpper⟩

theorem greenbaumVhat_orthonormal : L.greenbaumVhatᵀ * L.greenbaumVhat = 1 :=
  dilationStack_orthonormal (k + 1) _ _ _ L.greenbaum_isometry_identity
    L.greenbaumKsucc_nilpotent

theorem greenbaumVhat_first :
    L.greenbaumVhat *ᵥ firstCoord (Nat.succ_pos k) =
      physicalFirst L.hk_pos L.normalizedV := by
  rw [greenbaumVhat, greenbaumCsucc, greenbaumKsucc,
    dilationStack_first (k + 1) (Nat.succ_pos k) _ _ L.normalizedRsucc_strictUpper]
  ext ri
  have h := congrFun (L.normalizedV_column_eq ⟨0, L.hk_pos⟩) ri.2
  simp only [physicalFirst]
  split_ifs
  · simpa [normalizedVsucc, ofCols] using h.symm
  · rfl

theorem greenbaumX_orthonormal : L.greenbaumXᵀ * L.greenbaumX = 1 :=
  leadCols_orthonormal _ L.greenbaumVhat_orthonormal


theorem greenbaumKsucc_norm_le_one : ‖L.greenbaumKsucc‖ ≤ 1 :=
  triangularK_norm_le_one (Nat.succ_pos k) L.normalizedVsucc L.greenbaumCsucc
    L.greenbaumKsucc L.greenbaum_isometry_identity

theorem greenbaumCsucc_norm_le_two : ‖L.greenbaumCsucc‖ ≤ 2 :=
  triangularC_norm_le_two (Nat.succ_pos k) L.normalizedRsucc L.normalizedVsucc
    L.greenbaum_isometry_identity

theorem greenbaumK_norm_le_one : ‖L.greenbaumK‖ ≤ 1 := by
  rw [← L.greenbaum_CK_blocks.2.1]
  exact (norm_leadBlock_le _).trans L.greenbaumKsucc_norm_le_one

theorem greenbaumC_norm_le_two : ‖L.greenbaumC‖ ≤ 2 := by
  rw [← L.greenbaum_CK_blocks.1]
  exact (norm_leadBlock_le _).trans L.greenbaumCsucc_norm_le_two

theorem normalizedCommutator_padRow :
    L.underlineTmat * L.normalizedR - L.normalizedRsucc * L.underlineTmat =
      padRow L.normalizedCommutator := by
  obtain ⟨hlead, hcol, hlast⟩ := L.normalizedRsucc_block
  exact saad_commutator_block L.hk_pos L.Tmat (L.β k) L.normalizedRsucc L.normalizedR _
    L.normalizedR_strictUpper hlead hcol hlast

theorem greenbaumL_commutator :
    L.underlineTmat * L.greenbaumK - L.greenbaumKsucc * L.underlineTmat =
      padRow L.greenbaumL :=
  saad_exchange L.hk_pos L.Tmat (L.β k) L.normalizedRsucc L.normalizedR
    L.normalizedCommutator L.normalizedRsucc_strictUpper L.leadBlock_normalizedRsucc
    L.normalizedCommutator_padRow

lemma greenbaumL_le_four_mul : ‖L.greenbaumL‖ ≤ 4 * ‖L.normalizedCommutator‖ := by
  calc
    ‖L.greenbaumL‖ ≤
        ‖L.greenbaumC‖ * ‖L.normalizedCommutator‖ * ‖L.greenbaumC‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 2 * ‖L.normalizedCommutator‖ * 2 := by
      gcongr
      · exact L.greenbaumC_norm_le_two
      · exact L.greenbaumC_norm_le_two
    _ = 4 * ‖L.normalizedCommutator‖ := by ring

lemma greenbaumL_bound :
    ‖L.greenbaumL‖ ≤ (38400 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by
  have h := L.greenbaumL_le_four_mul
  have hM := L.normalizedCommutator_bound
  nlinarith

theorem greenbaum_power_exchange (r : ℕ) :
    L.underlineTmat * L.greenbaumK ^ r - L.greenbaumKsucc ^ r * L.underlineTmat =
      padRow (L.greenbaumD r) :=
  power_exchange_of_commutator L.underlineTmat L.greenbaumKsucc L.greenbaumK L.greenbaumL
    (triangularK_upper (Nat.succ_pos k) _ L.normalizedRsucc_strictUpper)
    L.greenbaum_CK_blocks.2.1 L.greenbaumL_commutator r

lemma greenbaumD_zero : L.greenbaumD 0 = 0 := rfl

lemma greenbaumD_succ (r : ℕ) :
    L.greenbaumD (r + 1) = L.greenbaumD r * L.greenbaumK + L.greenbaumK ^ r * L.greenbaumL :=
  rfl

theorem greenbaumD_norm (r : ℕ) : ‖L.greenbaumD r‖ ≤ (r : ℝ) * ‖L.greenbaumL‖ :=
  powerResidual_norm L.hk_pos _ _ L.greenbaumK_norm_le_one r


theorem greenbaumErrorBlock_eq (r : ℕ) :
    L.greenbaumErrorBlock r =
      L.normalizedFmat * L.greenbaumC * L.greenbaumK ^ r +
        L.normalizedV * (L.greenbaumD r - L.greenbaumD (r + 1)) :=
  rfl

lemma greenbaumCsucc_eq : L.greenbaumCsucc = 1 - L.greenbaumKsucc := by
  rw [greenbaumKsucc, triangularK]; abel

lemma greenbaumC_eq : L.greenbaumC = 1 - L.greenbaumK := by
  rw [greenbaumK, triangularK]; abel

theorem greenbaum_block_recurrence (r : ℕ) :
    L.H * L.greenbaumVBlock r =
      L.greenbaumVhatBlock r * L.underlineTmat + L.greenbaumErrorBlock r :=
  saad_block_recurrence L.H L.normalizedVsucc L.normalizedV L.normalizedFmat
    L.underlineTmat L.greenbaumCsucc L.greenbaumKsucc L.greenbaumC L.greenbaumK
    L.greenbaumD L.leadCols_normalizedVsucc L.normalized_governing_succ
    L.greenbaumCsucc_eq L.greenbaumC_eq L.greenbaum_power_exchange r

theorem greenbaum_dilation_recurrence :
    L.greenbaumBlockOperator * L.greenbaumX =
      L.greenbaumVhat * L.underlineTmat + L.greenbaumError :=
  saad_dilation_recurrence L.H L.normalizedVsucc L.normalizedV L.normalizedFmat
    L.underlineTmat L.greenbaumCsucc L.greenbaumKsucc L.greenbaumC L.greenbaumK
    L.greenbaumD L.leadCols_greenbaumVhatBlock L.leadCols_normalizedVsucc
    L.normalized_governing_succ L.greenbaumCsucc_eq L.greenbaumC_eq
    L.greenbaum_power_exchange

/-- The displayed block-error bound in the proof of `lem:dilated-recurrence`. -/
theorem greenbaumErrorBlock_norm_sqrt (r : ℕ) (hr : r ≤ k) :
    ‖L.greenbaumErrorBlock r‖ ≤
      2 * ‖L.normalizedFmat‖ + (2 * (k : ℝ) + 1) * Real.sqrt (k : ℝ) * ‖L.greenbaumL‖ := by
  have h := physicalErrorBlock_norm_le L.hk_pos L.normalizedV L.normalizedFmat
    L.greenbaumC L.greenbaumK L.greenbaumD ‖L.greenbaumL‖ r
    L.greenbaumC_norm_le_two L.greenbaumK_norm_le_one L.greenbaumD_norm
  have hrk : (r : ℝ) ≤ k := by exact_mod_cast hr
  exact h.trans (by gcongr; exact L.normalizedV_norm_sqrt)

/-- Stacking the blocks with √(k+1), exactly as in the paper. -/
theorem greenbaumError_norm_sqrt :
    ‖L.greenbaumError‖ ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) *
      (2 * ‖L.normalizedFmat‖ + (2 * (k : ℝ) + 1) * Real.sqrt (k : ℝ) * ‖L.greenbaumL‖) := by
  exact norm_stackBlocks_le_sqrt (fun r : Fin (k + 1) => L.greenbaumErrorBlock r.1)
    _ (by positivity) (fun r => L.greenbaumErrorBlock_norm_sqrt r.1 (by omega))

theorem greenbaumErrorBlock_norm (r : ℕ) (hr : r ≤ k) :
    ‖L.greenbaumErrorBlock r‖ ≤
      2 * ‖L.normalizedFmat‖ + (2 * (k : ℝ) + 1) * (k : ℝ) * ‖L.greenbaumL‖ := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have hs : Real.sqrt (k : ℝ) ≤ k := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg k), Real.sqrt_nonneg (k : ℝ)]
  exact (L.greenbaumErrorBlock_norm_sqrt r hr).trans (by gcongr)

theorem greenbaumErrorBlock_bound (r : ℕ) (hr : r ≤ k) :
    ‖L.greenbaumErrorBlock r‖ ≤ (120000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖ := by
  have h := L.greenbaumErrorBlock_norm r hr
  have hF := L.normalizedFmat_bound
  have hL := L.greenbaumL_bound
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have hs : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
  have hk2 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 5 := pow_le_pow_right₀ hk1 (by norm_num)
  have hk4 : (k : ℝ) ^ 4 ≤ (k : ℝ) ^ 5 := pow_le_pow_right₀ hk1 (by norm_num)
  have hcoef : 0 ≤ (2 * (k : ℝ) + 1) * (k : ℝ) := by positivity
  calc
    ‖L.greenbaumErrorBlock r‖ ≤
        2 * ‖L.normalizedFmat‖ + (2 * (k : ℝ) + 1) * (k : ℝ) * ‖L.greenbaumL‖ := h
    _ ≤ 2 * ((1500 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖) +
        (2 * (k : ℝ) + 1) * (k : ℝ) * ((38400 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖) := by
      gcongr
    _ = (3000 * (k : ℝ) ^ 2 + 76800 * (k : ℝ) ^ 5 + 38400 * (k : ℝ) ^ 4) *
        (L.ε * ‖L.H‖) := by ring
    _ ≤ (3000 * (k : ℝ) ^ 5 + 76800 * (k : ℝ) ^ 5 + 38400 * (k : ℝ) ^ 5) *
        (L.ε * ‖L.H‖) := by gcongr
    _ ≤ (120000 * (k : ℝ) ^ 5) * (L.ε * ‖L.H‖) := by
      apply mul_le_mul_of_nonneg_right _ hs
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ k by positivity) 5]
    _ = (120000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖ := by ring

theorem greenbaumError_bound :
    ‖L.greenbaumError‖ ≤ (240000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ := by
  have hR : 0 ≤ (120000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖ :=
    mul_nonneg (mul_nonneg (by positivity) L.hε_nonneg) (norm_nonneg _)
  have hs := norm_stackBlocks_le (Nat.succ_pos k)
    (fun r : Fin (k + 1) => L.greenbaumErrorBlock r.1)
    ((120000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖) hR
    (fun r => L.greenbaumErrorBlock_bound r.1 (Nat.lt_succ_iff.mp r.2))
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have hE : L.greenbaumError =
      stackBlocks (fun r : Fin (k + 1) => L.greenbaumErrorBlock r.1) := rfl
  rw [hE]
  calc
    _ ≤ ((k + 1 : ℕ) : ℝ) * ((120000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖) := hs
    _ ≤ (2 * (k : ℝ)) * ((120000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖) := by
      apply mul_le_mul_of_nonneg_right _ hR
      push_cast; linarith
    _ = (240000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ := by ring

end LanczosRun
end FinitePrecisionLanczos
