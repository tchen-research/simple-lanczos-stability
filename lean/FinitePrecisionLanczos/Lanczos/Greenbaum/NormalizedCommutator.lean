import FinitePrecisionLanczos.Lanczos.Greenbaum.NormalizedRecurrence

/-!
# Paige's identity in the normalized coordinates

This file proves the norm estimate in `lem:normalized-commutator`.  The proof
is an exact change of coordinates applied to `lem:gram-commutator`; the
three summands in `normalized_commutator_transfer` are the transported local
error terms.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

lemma invNormDiag_transpose : L.invNormDiagᵀ = L.invNormDiag := by
  simp [invNormDiag]

/-- Exact normalized boundary overlap `a=Vᵀw`. -/
noncomputable def normalizedA : Vec k := L.normalizedVᵀ *ᵥ L.normalizedVNext

/-- The matrix `M=T_k U-U T_k-b a e_kᵀ` in
`lem:normalized-commutator`. -/
noncomputable def normalizedCommutator : Mat k k :=
  L.Tmat * L.normalizedU - L.normalizedU * L.Tmat -
    L.normalizedBeta • lastOuter L.hk_pos L.normalizedA

/-- Diagonal inverse defect used only for estimating the coordinate change. -/
noncomputable def invNormDefect : Mat k k := L.invNormDiag - 1

/-- `TZ-ZT`, where `Z=D⁻¹`. -/
noncomputable def normalizationDiagonalCommutator : Mat k k :=
  L.Tmat * L.invNormDiag - L.invNormDiag * L.Tmat

/-- The raw upper-triangular Paige error after removing its boundary term. -/
def rawUpperError : Mat k k := L.Amat - L.Cmat

theorem normalized_gram_conjugation :
    L.normalizedVᵀ * L.normalizedV =
      L.invNormDiag * (L.Vmatᵀ * L.Vmat) * L.invNormDiag := by
  simp [normalizedV, Matrix.transpose_mul, L.invNormDiag_transpose,
    Matrix.mul_assoc]

/-- The strict upper Gram matrix changes coordinates as `U=Z R Z`. -/
theorem normalizedU_eq_conjugated_Rmat :
    L.normalizedU = L.invNormDiag * L.Rmat * L.invNormDiag := by
  ext i j
  by_cases hij : i.1 < j.1
  · have hne : i ≠ j := by intro h; subst j; omega
    rw [normalizedU]
    simp only [hij, if_true]
    rw [L.normalized_gram_conjugation]
    simp [invNormDiag, Rmat, hij, Omega, hne,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
  · simp [normalizedU, hij, invNormDiag, Rmat,
      Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- The projected normalized boundary is the conjugate of `C_k`. -/
theorem normalized_boundary_projection :
    L.invNormDiag * L.Cmat * L.invNormDiag =
      L.normalizedBeta • lastOuter L.hk_pos L.normalizedA := by
  calc
    L.invNormDiag * L.Cmat * L.invNormDiag =
        L.normalizedVᵀ * (L.boundary * L.invNormDiag) := by
      simp only [Cmat, normalizedV, Matrix.transpose_mul,
        L.invNormDiag_transpose]
      simp [Matrix.mul_assoc]
    _ = L.normalizedVᵀ *
        (L.normalizedBeta • lastOuter L.hk_pos L.normalizedVNext) := by
      rw [L.boundary_mul_invNormDiag]
    _ = L.normalizedBeta •
        lastOuter L.hk_pos (L.normalizedVᵀ *ᵥ L.normalizedVNext) := by
      rw [Matrix.mul_smul, mul_lastOuter]
    _ = L.normalizedBeta • lastOuter L.hk_pos L.normalizedA := rfl

theorem rawUpperError_eq :
    L.rawUpperError = L.Nmat + L.upG - L.upQ := by
  rw [rawUpperError, L.upper_commutator]
  abel

/-- Exact three-term transport identity for the normalized commutator. -/
theorem normalized_commutator_transfer :
    L.normalizedCommutator =
      L.normalizationDiagonalCommutator * L.Rmat * L.invNormDiag +
      L.invNormDiag * L.rawUpperError * L.invNormDiag +
      L.invNormDiag * L.Rmat * L.normalizationDiagonalCommutator := by
  rw [normalizedCommutator, L.normalizedU_eq_conjugated_Rmat,
    ← L.normalized_boundary_projection]
  simp only [normalizationDiagonalCommutator, rawUpperError, Amat]
  noncomm_ring

/-! ## Explicit bounds -/

lemma invNormDefect_norm_bound : ‖L.invNormDefect‖ ≤ 2 * L.ε := by
  have hdiag : L.invNormDefect = Matrix.diagonal fun j =>
      (L.columnNorm j)⁻¹ - 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [invNormDefect, invNormDiag]
    · simp [invNormDefect, invNormDiag, hij]
  rw [hdiag, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) L.hε_nonneg)).2
  intro j
  simpa [Real.norm_eq_abs] using L.invColumnNorm_abs_sub_one j

lemma normalizationDiagonalCommutator_as_defect :
    L.normalizationDiagonalCommutator =
      L.Tmat * L.invNormDefect - L.invNormDefect * L.Tmat := by
  simp only [normalizationDiagonalCommutator, invNormDefect]
  noncomm_ring

lemma normalizationDiagonalCommutator_bound :
    ‖L.normalizationDiagonalCommutator‖ ≤
      (1200 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by
  rw [L.normalizationDiagonalCommutator_as_defect]
  calc
    ‖L.Tmat * L.invNormDefect - L.invNormDefect * L.Tmat‖ ≤
        ‖L.Tmat * L.invNormDefect‖ + ‖L.invNormDefect * L.Tmat‖ :=
      norm_sub_le _ _
    _ ≤ ‖L.Tmat‖ * ‖L.invNormDefect‖ +
        ‖L.invNormDefect‖ * ‖L.Tmat‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ((300 * (k : ℝ) ^ 3) * ‖L.H‖) * (2 * L.ε) +
        (2 * L.ε) * ((300 * (k : ℝ) ^ 3) * ‖L.H‖) := by
      exact add_le_add
        (mul_le_mul L.Tmat_norm_bound L.invNormDefect_norm_bound
          (norm_nonneg _) (by positivity))
        (mul_le_mul L.invNormDefect_norm_bound L.Tmat_norm_bound
          (norm_nonneg _) (mul_nonneg (by norm_num) L.hε_nonneg))
    _ = (1200 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by ring

lemma Rmat_entry_bound_four (i j : Fin k) : |L.Rmat i j| ≤ 4 := by
  by_cases hij : i.1 < j.1
  · have hne : i ≠ j := by intro h; subst j; omega
    rw [Rmat, if_pos hij, L.Omega_offdiag i j hne]
    have hi : vnorm (L.v (i.1 + 1)) ≤ 2 := by
      simpa only [Nat.succ_eq_add_one] using
        L.vnorm_v_le_two (by omega) (Nat.succ_le_iff.mpr i.2)
    have hj : vnorm (L.v (j.1 + 1)) ≤ 2 := by
      simpa only [Nat.succ_eq_add_one] using
        L.vnorm_v_le_two (by omega) (Nat.succ_le_iff.mpr j.2)
    calc
      |vdot (L.v (i.1 + 1)) (L.v (j.1 + 1))| ≤
          vnorm (L.v (i.1 + 1)) * vnorm (L.v (j.1 + 1)) := abs_vdot_le _ _
      _ ≤ 2 * 2 := mul_le_mul hi hj (vnorm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  · simp [Rmat, hij]

lemma Rmat_norm_bound_four : ‖L.Rmat‖ ≤ 4 * (k : ℝ) ^ 2 := by
  have h := norm_le_card_mul_card_mul_of_entry_bound L.Rmat 4 (by norm_num)
    L.Rmat_entry_bound_four
  calc
    ‖L.Rmat‖ ≤ (k : ℝ) * (k : ℝ) * 4 := h
    _ = 4 * (k : ℝ) ^ 2 := by ring

lemma rawUpperError_entry_bound (i j : Fin k) :
    |L.rawUpperError i j| ≤
      (5800 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  let B : ℝ := (1200 * (k : ℝ)) * L.ε * ‖L.H‖
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) L.hε_nonneg)
      (norm_nonneg _)
  have hp0 := L.p_bound_all i.1 (Nat.le_of_lt i.2)
  have hp1 := L.p_bound_all (i.1 + 1) (Nat.succ_le_iff.mpr i.2)
  have hN : |L.Nmat i j| ≤ 2 * B := by
    by_cases hij : i = j
    · subst j
      simp only [Nmat, Matrix.diagonal_apply_eq]
      calc
        |L.p i.1 - L.p (i.1 + 1)| ≤ |L.p i.1| + |L.p (i.1 + 1)| := by
          simpa using abs_sub_le (L.p i.1) 0 (L.p (i.1 + 1))
        _ ≤ B + B := by simpa [B] using add_le_add hp0 hp1
        _ = 2 * B := by ring
    · simp [Nmat, hij, hB]
  have hG : |L.upG i j| ≤ (2800 * (k : ℝ)) * L.ε * ‖L.H‖ := by
    by_cases hij : i.1 < j.1
    · simpa [upG, hij] using L.Gmat_entry_bound i j
    · rw [upG, if_neg hij, abs_zero]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) L.hε_nonneg)
        (norm_nonneg _)
  have hQ : |L.upQ i j| ≤ (600 * (k : ℝ)) * L.ε * ‖L.H‖ := by
    by_cases hij : i.1 < j.1
    · simpa [upQ, hij] using L.Qmat_entry_bound i j
    · rw [upQ, if_neg hij, abs_zero]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) L.hε_nonneg)
        (norm_nonneg _)
  rw [L.rawUpperError_eq]
  calc
    |(L.Nmat + L.upG - L.upQ) i j| ≤
        |L.Nmat i j| + |L.upG i j| + |L.upQ i j| := by
      simp only [Matrix.sub_apply, Matrix.add_apply]
      calc
        |L.Nmat i j + L.upG i j - L.upQ i j| ≤
            |L.Nmat i j + L.upG i j| + |L.upQ i j| := by
          simpa using abs_sub_le (L.Nmat i j + L.upG i j) 0 (L.upQ i j)
        _ ≤ |L.Nmat i j| + |L.upG i j| + |L.upQ i j| :=
          add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 2 * B + (2800 * (k : ℝ)) * L.ε * ‖L.H‖ +
        (600 * (k : ℝ)) * L.ε * ‖L.H‖ := by
      gcongr
    _ = (5800 * (k : ℝ)) * L.ε * ‖L.H‖ := by
      simp [B]
      ring

lemma rawUpperError_bound :
    ‖L.rawUpperError‖ ≤ (5800 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by
  have h := norm_le_card_mul_card_mul_of_entry_bound L.rawUpperError
    ((5800 * (k : ℝ)) * L.ε * ‖L.H‖)
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) L.hε_nonneg)
      (norm_nonneg _))
    L.rawUpperError_entry_bound
  calc
    ‖L.rawUpperError‖ ≤
        (k : ℝ) * (k : ℝ) * ((5800 * (k : ℝ)) * L.ε * ‖L.H‖) := h
    _ = (5800 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by ring

/-- Explicit version of the norm estimate in
`lem:normalized-commutator`. -/
theorem normalizedCommutator_bound :
    ‖L.normalizedCommutator‖ ≤
      (50000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hscale : 0 ≤ L.ε * ‖L.H‖ :=
    mul_nonneg L.hε_nonneg (norm_nonneg _)
  let BJ : ℝ := (1200 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖
  let BR : ℝ := 4 * (k : ℝ) ^ 2
  let BE : ℝ := (5800 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖
  have hBJ : 0 ≤ BJ := by
    dsimp [BJ]
    exact mul_nonneg
      (mul_nonneg
        (show 0 ≤ (1200 : ℝ) * (k : ℝ) ^ 3 by positivity) L.hε_nonneg)
      (norm_nonneg _)
  have hBR : 0 ≤ BR := by dsimp [BR]; positivity
  have hBE : 0 ≤ BE := by
    dsimp [BE]
    exact mul_nonneg
      (mul_nonneg
        (show 0 ≤ (5800 : ℝ) * (k : ℝ) ^ 3 by positivity) L.hε_nonneg)
      (norm_nonneg _)
  have hterm1 :
      ‖L.normalizationDiagonalCommutator * L.Rmat * L.invNormDiag‖ ≤
        BJ * BR * 2 := by
    calc
      ‖L.normalizationDiagonalCommutator * L.Rmat * L.invNormDiag‖ ≤
          ‖L.normalizationDiagonalCommutator * L.Rmat‖ * ‖L.invNormDiag‖ :=
        norm_mul_le _ _
      _ ≤ (‖L.normalizationDiagonalCommutator‖ * ‖L.Rmat‖) *
          ‖L.invNormDiag‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (BJ * BR) * 2 :=
        mul_le_mul
          (mul_le_mul L.normalizationDiagonalCommutator_bound L.Rmat_norm_bound_four
            (norm_nonneg _) hBJ)
          L.invNormDiag_norm_le_two (norm_nonneg _) (mul_nonneg hBJ hBR)
  have hterm2 :
      ‖L.invNormDiag * L.rawUpperError * L.invNormDiag‖ ≤ 2 * BE * 2 := by
    calc
      ‖L.invNormDiag * L.rawUpperError * L.invNormDiag‖ ≤
          ‖L.invNormDiag * L.rawUpperError‖ * ‖L.invNormDiag‖ := norm_mul_le _ _
      _ ≤ (‖L.invNormDiag‖ * ‖L.rawUpperError‖) * ‖L.invNormDiag‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (2 * BE) * 2 :=
        mul_le_mul
          (mul_le_mul L.invNormDiag_norm_le_two L.rawUpperError_bound
            (norm_nonneg _) (by norm_num))
          L.invNormDiag_norm_le_two (norm_nonneg _) (mul_nonneg (by norm_num) hBE)
  have hterm3 :
      ‖L.invNormDiag * L.Rmat * L.normalizationDiagonalCommutator‖ ≤
        2 * BR * BJ := by
    calc
      ‖L.invNormDiag * L.Rmat * L.normalizationDiagonalCommutator‖ ≤
          ‖L.invNormDiag * L.Rmat‖ * ‖L.normalizationDiagonalCommutator‖ :=
        norm_mul_le _ _
      _ ≤ (‖L.invNormDiag‖ * ‖L.Rmat‖) *
          ‖L.normalizationDiagonalCommutator‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (2 * BR) * BJ :=
        mul_le_mul
          (mul_le_mul L.invNormDiag_norm_le_two L.Rmat_norm_bound_four
            (norm_nonneg _) (by norm_num))
          L.normalizationDiagonalCommutator_bound (norm_nonneg _)
            (mul_nonneg (by norm_num) hBR)
  rw [L.normalized_commutator_transfer]
  calc
    ‖L.normalizationDiagonalCommutator * L.Rmat * L.invNormDiag +
        L.invNormDiag * L.rawUpperError * L.invNormDiag +
        L.invNormDiag * L.Rmat * L.normalizationDiagonalCommutator‖ ≤
      ‖L.normalizationDiagonalCommutator * L.Rmat * L.invNormDiag‖ +
        ‖L.invNormDiag * L.rawUpperError * L.invNormDiag‖ +
        ‖L.invNormDiag * L.Rmat * L.normalizationDiagonalCommutator‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((1200 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖) *
          (4 * (k : ℝ) ^ 2) * 2 +
        2 * ((5800 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖) * 2 +
        2 * (4 * (k : ℝ) ^ 2) *
          ((1200 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖) := by
      simpa [BJ, BR, BE] using add_le_add (add_le_add hterm1 hterm2) hterm3
    _ ≤ (50000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖ := by
      have hk35 : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 5 := by
        nlinarith [sq_nonneg (k : ℝ),
          mul_nonneg (show 0 ≤ (k : ℝ) ^ 3 by positivity)
            (show 0 ≤ (k : ℝ) ^ 2 - 1 by nlinarith [sq_nonneg ((k : ℝ) - 1)])]
      calc
        ((1200 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖) *
              (4 * (k : ℝ) ^ 2) * 2 +
            2 * ((5800 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖) * 2 +
            2 * (4 * (k : ℝ) ^ 2) *
              ((1200 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖)
          = (19200 * (k : ℝ) ^ 5 + 23200 * (k : ℝ) ^ 3) *
              (L.ε * ‖L.H‖) := by ring
        _ ≤ (19200 * (k : ℝ) ^ 5 + 23200 * (k : ℝ) ^ 5) *
              (L.ε * ‖L.H‖) := by
          have hmiddle : 23200 * (k : ℝ) ^ 3 ≤ 23200 * (k : ℝ) ^ 5 :=
            mul_le_mul_of_nonneg_left hk35 (by norm_num)
          exact mul_le_mul_of_nonneg_right
            (by simpa [add_comm] using
              add_le_add_left hmiddle (19200 * (k : ℝ) ^ 5)) hscale
        _ = (42400 * (k : ℝ) ^ 5) * (L.ε * ‖L.H‖) := by ring
        _ ≤ (50000 * (k : ℝ) ^ 5) * (L.ε * ‖L.H‖) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num)
              (show 0 ≤ (k : ℝ) ^ 5 by positivity)) hscale
        _ = (50000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖ := by ring

end LanczosRun
end FinitePrecisionLanczos
