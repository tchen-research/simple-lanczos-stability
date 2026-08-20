import FinitePrecisionLanczos.Lanczos.Greenbaum.Normalization










namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)



noncomputable def normalizationCoeffError : Mat k k :=
  L.normDiag * L.Tmat * L.invNormDiag - L.Tmat


noncomputable def normalizedE : Mat n k :=
  L.normalizedV * L.normalizationCoeffError + L.Fmat * L.invNormDiag

theorem normalizedV_mul_normDiag :
    L.normalizedV * L.normDiag = L.Vmat := by
  rw [normalizedV, Matrix.mul_assoc, L.invNormDiag_mul_normDiag,
    Matrix.mul_one]

theorem normalizedV_mul_coefficients :
    L.Vmat * L.Tmat * L.invNormDiag =
      L.normalizedV * L.Tmat + L.normalizedV * L.normalizationCoeffError := by
  calc
    L.Vmat * L.Tmat * L.invNormDiag =
        (L.normalizedV * L.normDiag) * L.Tmat * L.invNormDiag := by
      rw [L.normalizedV_mul_normDiag]
    _ = L.normalizedV * (L.normDiag * L.Tmat * L.invNormDiag) := by
      simp [Matrix.mul_assoc]
    _ = L.normalizedV * L.Tmat +
        L.normalizedV * L.normalizationCoeffError := by
      rw [normalizationCoeffError, Matrix.mul_sub]
      abel


theorem normalized_governing :
    L.H * L.normalizedV =
      L.normalizedV * L.Tmat +
        L.normalizedBeta • lastOuter L.hk_pos L.normalizedVNext + L.normalizedE := by
  calc
    L.H * L.normalizedV = (L.H * L.Vmat) * L.invNormDiag := by
      rw [normalizedV, Matrix.mul_assoc]
    _ = (L.Vmat * L.Tmat + L.boundary + L.Fmat) * L.invNormDiag := by
      rw [L.governing_matrix]
    _ = L.Vmat * L.Tmat * L.invNormDiag +
        L.boundary * L.invNormDiag + L.Fmat * L.invNormDiag := by
      rw [Matrix.add_mul, Matrix.add_mul]
    _ = (L.normalizedV * L.Tmat +
          L.normalizedV * L.normalizationCoeffError) +
        L.normalizedBeta • lastOuter L.hk_pos L.normalizedVNext +
          L.Fmat * L.invNormDiag := by
      rw [L.normalizedV_mul_coefficients, L.boundary_mul_invNormDiag]
    _ = L.normalizedV * L.Tmat +
        L.normalizedBeta • lastOuter L.hk_pos L.normalizedVNext + L.normalizedE := by
      simp only [normalizedE]
      abel

lemma normalizationCoeffError_apply (i j : Fin k) :
    L.normalizationCoeffError i j =
      (L.columnNorm i * (L.columnNorm j)⁻¹ - 1) * L.Tmat i j := by
  simp [normalizationCoeffError, normDiag, invNormDiag,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

lemma normalization_ratio_bound (i j : Fin k) :
    |L.columnNorm i * (L.columnNorm j)⁻¹ - 1| ≤ 4 * L.ε := by
  have hi := L.columnNorm_abs_sub_one i
  have hj := L.invColumnNorm_abs_sub_one j
  have hz := L.invColumnNorm_le_two j
  have hz0 := L.invColumnNorm_nonneg j
  calc
    |L.columnNorm i * (L.columnNorm j)⁻¹ - 1|
        = |(L.columnNorm i - 1) * (L.columnNorm j)⁻¹ +
            ((L.columnNorm j)⁻¹ - 1)| := by ring_nf
    _ ≤ |L.columnNorm i - 1| * |(L.columnNorm j)⁻¹| +
          |(L.columnNorm j)⁻¹ - 1| := by
      exact (abs_add_le _ _).trans_eq (by rw [abs_mul])
    _ ≤ L.ε * 2 + 2 * L.ε := by
      have habs : |(L.columnNorm j)⁻¹| ≤ 2 := by
        simpa [abs_of_nonneg hz0] using hz
      exact add_le_add
        (mul_le_mul hi habs (abs_nonneg _) L.hε_nonneg) hj
    _ = 4 * L.ε := by ring



lemma normalizationCoeffError_entry_bound (i j : Fin k) :
    |L.normalizationCoeffError i j| ≤
      (1200 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  rw [L.normalizationCoeffError_apply, abs_mul]
  have hr := L.normalization_ratio_bound i j
  have ht := L.Tmat_entry_bound i j
  calc
    |L.columnNorm i * (L.columnNorm j)⁻¹ - 1| * |L.Tmat i j|
        ≤ (4 * L.ε) * ((300 * (k : ℝ)) * ‖L.H‖) :=
      mul_le_mul hr ht (abs_nonneg _) (mul_nonneg (by positivity) L.hε_nonneg)
    _ = (1200 * (k : ℝ)) * L.ε * ‖L.H‖ := by ring

lemma normalizationCoeffError_bound :
    ‖L.normalizationCoeffError‖ ≤
      (1200 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by
  have h := norm_le_card_mul_card_mul_of_entry_bound
    L.normalizationCoeffError ((1200 * (k : ℝ)) * L.ε * ‖L.H‖)
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) L.hε_nonneg)
      (norm_nonneg _))
    L.normalizationCoeffError_entry_bound
  calc
    ‖L.normalizationCoeffError‖ ≤
        (k : ℝ) * (k : ℝ) * ((1200 * (k : ℝ)) * L.ε * ‖L.H‖) := h
    _ = (1200 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by ring



theorem normalizedE_bound :
    ‖L.normalizedE‖ ≤ (2600 * (k : ℝ) ^ 4) * L.ε * ‖L.H‖ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hscale : 0 ≤ L.ε * ‖L.H‖ :=
    mul_nonneg L.hε_nonneg (norm_nonneg _)
  have hfirst : ‖L.normalizedV * L.normalizationCoeffError‖ ≤
      (1200 * (k : ℝ) ^ 4) * L.ε * ‖L.H‖ := by
    calc
      ‖L.normalizedV * L.normalizationCoeffError‖ ≤
          ‖L.normalizedV‖ * ‖L.normalizationCoeffError‖ := norm_mul_le _ _
      _ ≤ (k : ℝ) * ((1200 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖) :=
        mul_le_mul L.normalizedV_norm L.normalizationCoeffError_bound
          (norm_nonneg _) hk0
      _ = (1200 * (k : ℝ) ^ 4) * L.ε * ‖L.H‖ := by ring
  have hsecond : ‖L.Fmat * L.invNormDiag‖ ≤
      (1400 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖ := by
    calc
      ‖L.Fmat * L.invNormDiag‖ ≤ ‖L.Fmat‖ * ‖L.invNormDiag‖ := norm_mul_le _ _
      _ ≤ ((700 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖) * 2 :=
        mul_le_mul L.Fmat_bound L.invNormDiag_norm_le_two
          (norm_nonneg _)
          (mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (k : ℝ))) L.hε_nonneg)
            (norm_nonneg _))
      _ = (1400 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖ := by ring
  have hkSq1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [sq_nonneg ((k : ℝ) - 1)]
  have hk24 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by
    have hp := mul_nonneg (sq_nonneg (k : ℝ)) (sub_nonneg.mpr hkSq1)
    nlinarith
  have hsecond' : ‖L.Fmat * L.invNormDiag‖ ≤
      (1400 * (k : ℝ) ^ 4) * L.ε * ‖L.H‖ := by
    calc
      ‖L.Fmat * L.invNormDiag‖ ≤
          (1400 * (k : ℝ) ^ 2) * L.ε * ‖L.H‖ := hsecond
      _ = (1400 * (k : ℝ) ^ 2) * (L.ε * ‖L.H‖) := by ring
      _ ≤ (1400 * (k : ℝ) ^ 4) * (L.ε * ‖L.H‖) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hk24 (by norm_num)) hscale
      _ = (1400 * (k : ℝ) ^ 4) * L.ε * ‖L.H‖ := by ring
  calc
    ‖L.normalizedE‖ ≤
        ‖L.normalizedV * L.normalizationCoeffError‖ +
          ‖L.Fmat * L.invNormDiag‖ := by
      exact norm_add_le _ _
    _ ≤ (1200 * (k : ℝ) ^ 4) * L.ε * ‖L.H‖ +
        (1400 * (k : ℝ) ^ 4) * L.ε * ‖L.H‖ :=
      add_le_add hfirst hsecond'
    _ = (2600 * (k : ℝ) ^ 4) * L.ε * ‖L.H‖ := by ring

end LanczosRun
end FinitePrecisionLanczos
