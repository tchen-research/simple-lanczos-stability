import FinitePrecisionLanczos.Core.DilationBounds








namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)


noncomputable def columnNorm (j : Fin k) : ℝ := vnorm (L.v (j.1 + 1))

noncomputable def normDiag : Mat k k := Matrix.diagonal L.columnNorm

noncomputable def invNormDiag : Mat k k :=
  Matrix.diagonal fun j => (L.columnNorm j)⁻¹


noncomputable def normalizedV : Mat n k := L.Vmat * L.invNormDiag

lemma columnNorm_sq_bounds (j : Fin k) :
    1 - L.ε ≤ L.columnNorm j ^ 2 ∧ L.columnNorm j ^ 2 ≤ 1 + L.ε :=
  L.near_unit_sq (by omega) (Nat.succ_le_iff.mpr j.2)

lemma columnNorm_lower (j : Fin k) : 1 - L.ε ≤ L.columnNorm j := by
  have hs := (L.columnNorm_sq_bounds j).1
  have hd := vnorm_nonneg (L.v (j.1 + 1))
  have he0 := L.hε_nonneg
  have he1 := L.epsilon_le_one
  have hone : 0 < 1 - L.ε := by
    linarith [L.epsilon_le_one_hundredth]
  by_contra h
  have hlt : L.columnNorm j < 1 - L.ε := lt_of_not_ge h
  have hsum : 0 < (1 - L.ε) + L.columnNorm j :=
    add_pos_of_pos_of_nonneg hone hd
  have hprod : 0 < ((1 - L.ε) - L.columnNorm j) *
      ((1 - L.ε) + L.columnNorm j) :=
    mul_pos (sub_pos.mpr hlt) hsum
  have hsq_lt : L.columnNorm j ^ 2 < (1 - L.ε) ^ 2 := by
    nlinarith
  have hsq_le : (1 - L.ε) ^ 2 ≤ 1 - L.ε := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr he1)]
  linarith

lemma columnNorm_upper (j : Fin k) : L.columnNorm j ≤ 1 + L.ε := by
  exact L.vnorm_v_le_one_add_epsilon (by omega) (Nat.succ_le_iff.mpr j.2)

lemma columnNorm_pos (j : Fin k) : 0 < L.columnNorm j := by
  have hl := L.columnNorm_lower j
  have he := L.epsilon_le_one_hundredth
  linarith

lemma columnNorm_ne_zero (j : Fin k) : L.columnNorm j ≠ 0 :=
  ne_of_gt (L.columnNorm_pos j)

lemma columnNorm_abs_sub_one (j : Fin k) :
    |L.columnNorm j - 1| ≤ L.ε := by
  rw [abs_le]
  constructor
  · linarith [L.columnNorm_lower j]
  · linarith [L.columnNorm_upper j]

lemma invColumnNorm_bounds (j : Fin k) :
    1 - 2 * L.ε ≤ (L.columnNorm j)⁻¹ ∧
      (L.columnNorm j)⁻¹ ≤ 1 + 2 * L.ε := by
  have hd := L.columnNorm_pos j
  have hlo := L.columnNorm_lower j
  have hup := L.columnNorm_upper j
  have he0 := L.hε_nonneg
  have he100 := L.epsilon_le_one_hundredth
  constructor
  · rw [show (L.columnNorm j)⁻¹ = 1 / L.columnNorm j by simp]
    rw [le_div_iff₀ hd]
    have hcoef : 0 ≤ 1 - 2 * L.ε := by linarith
    calc
      (1 - 2 * L.ε) * L.columnNorm j ≤
          (1 - 2 * L.ε) * (1 + L.ε) :=
        mul_le_mul_of_nonneg_left hup hcoef
      _ ≤ 1 := by nlinarith [sq_nonneg L.ε]
  · rw [show (L.columnNorm j)⁻¹ = 1 / L.columnNorm j by simp]
    rw [div_le_iff₀ hd]
    calc
      1 ≤ (1 + 2 * L.ε) * (1 - L.ε) := by
        nlinarith [mul_nonneg L.hε_nonneg
          (sub_nonneg.mpr L.epsilon_le_one_hundredth)]
      _ ≤ (1 + 2 * L.ε) * L.columnNorm j := by
        exact mul_le_mul_of_nonneg_left hlo (by linarith)

lemma invColumnNorm_abs_sub_one (j : Fin k) :
    |(L.columnNorm j)⁻¹ - 1| ≤ 2 * L.ε := by
  rw [abs_le]
  constructor <;> linarith [L.invColumnNorm_bounds j]

lemma invColumnNorm_le_two (j : Fin k) : (L.columnNorm j)⁻¹ ≤ 2 := by
  have := (L.invColumnNorm_bounds j).2
  have := L.epsilon_le_one_hundredth
  linarith

lemma invColumnNorm_nonneg (j : Fin k) : 0 ≤ (L.columnNorm j)⁻¹ :=
  (L.columnNorm_pos j).le |> inv_nonneg.mpr

theorem normDiag_mul_invNormDiag : L.normDiag * L.invNormDiag = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [normDiag, invNormDiag, L.columnNorm_ne_zero]
  · simp [normDiag, invNormDiag, hij]

theorem invNormDiag_mul_normDiag : L.invNormDiag * L.normDiag = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [normDiag, invNormDiag, L.columnNorm_ne_zero]
  · simp [normDiag, invNormDiag, hij]

lemma invNormDiag_norm_le_two : ‖L.invNormDiag‖ ≤ 2 := by
  rw [invNormDiag, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (L.invColumnNorm_nonneg j)]
  exact L.invColumnNorm_le_two j

lemma normalizedV_apply (i : Fin n) (j : Fin k) :
    L.normalizedV i j = (L.columnNorm j)⁻¹ * L.v (j.1 + 1) i := by
  simp [normalizedV, Vmat, invNormDiag, Matrix.mul_diagonal, mul_comm]

lemma normalizedV_column (j : Fin k) :
    (fun i => L.normalizedV i j) = (L.columnNorm j)⁻¹ • L.v (j.1 + 1) := by
  ext i
  simp [L.normalizedV_apply, Pi.smul_apply]


theorem normalizedV_unit (j : Fin k) :
    vnorm (fun i => L.normalizedV i j) = 1 := by
  rw [L.normalizedV_column, vnorm_smul]
  rw [abs_of_nonneg (L.invColumnNorm_nonneg j)]
  dsimp [columnNorm]
  exact inv_mul_cancel₀ (L.columnNorm_ne_zero j)

lemma normalizedV_norm : ‖L.normalizedV‖ ≤ (k : ℝ) := by
  calc
    ‖L.normalizedV‖ ≤ ∑ j : Fin k, vnorm (fun i => L.normalizedV i j) :=
      norm_ofCols_le_sum _
    _ = (k : ℝ) := by simp [L.normalizedV_unit]


noncomputable def normalizedU : Mat k k := fun i j =>
  if i.1 < j.1 then (L.normalizedVᵀ * L.normalizedV) i j else 0

lemma normalizedU_strictUpper : StrictUpper L.normalizedU := by
  intro i j hij
  simp [normalizedU, hij]

lemma normalizedGram_diag (j : Fin k) :
    (L.normalizedVᵀ * L.normalizedV) j j = 1 := by
  have hsq := vnorm_sq (fun i => L.normalizedV i j)
  rw [L.normalizedV_unit] at hsq
  simpa [Matrix.mul_apply, vdot, dotProduct] using hsq.symm


theorem normalized_gram_split :
    L.normalizedVᵀ * L.normalizedV = 1 + L.normalizedU + L.normalizedUᵀ := by
  ext i j
  rcases lt_trichotomy i.1 j.1 with hij | hij | hij
  · have hne : i ≠ j := by intro h; subst j; omega
    simp [normalizedU, hij, not_lt_of_ge hij.le, hne]
  · have heq : i = j := Fin.ext hij
    subst j
    simp [normalizedU, L.normalizedGram_diag]
  · have hji : j.1 < i.1 := hij
    have hne : i ≠ j := by intro h; subst j; omega
    have hsym : (L.normalizedVᵀ * L.normalizedV) j i =
        (L.normalizedVᵀ * L.normalizedV) i j := by
      simp [Matrix.mul_apply]
      exact dotProduct_comm _ _
    simp [normalizedU, hji, not_lt_of_ge hji.le, hne, hsym]




noncomputable def nextColumnNorm : ℝ := vnorm (L.v (k + 1))

lemma nextColumnNorm_sq_bounds (hb : L.β k ≠ 0) :
    1 - L.ε ≤ L.nextColumnNorm ^ 2 ∧
      L.nextColumnNorm ^ 2 ≤ 1 + L.ε := by
  have h := abs_le.mp (L.hnext hb)
  constructor
  · dsimp [nextColumnNorm]
    linarith [h.1]
  · dsimp [nextColumnNorm]
    linarith [h.2]

lemma nextColumnNorm_lower (hb : L.β k ≠ 0) :
    1 - L.ε ≤ L.nextColumnNorm := by
  have hs := (L.nextColumnNorm_sq_bounds hb).1
  have hd := vnorm_nonneg (L.v (k + 1))
  have he0 := L.hε_nonneg
  have he1 := L.epsilon_le_one
  have hone : 0 < 1 - L.ε := by
    linarith [L.epsilon_le_one_hundredth]
  by_contra h
  have hlt : L.nextColumnNorm < 1 - L.ε := lt_of_not_ge h
  have hsum : 0 < (1 - L.ε) + L.nextColumnNorm :=
    add_pos_of_pos_of_nonneg hone hd
  have hprod : 0 < ((1 - L.ε) - L.nextColumnNorm) *
      ((1 - L.ε) + L.nextColumnNorm) :=
    mul_pos (sub_pos.mpr hlt) hsum
  have hsq_lt : L.nextColumnNorm ^ 2 < (1 - L.ε) ^ 2 := by
    nlinarith
  have hsq_le : (1 - L.ε) ^ 2 ≤ 1 - L.ε := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr he1)]
  linarith

lemma nextColumnNorm_pos (hb : L.β k ≠ 0) : 0 < L.nextColumnNorm := by
  have h := L.nextColumnNorm_lower hb
  linarith [L.epsilon_le_one_hundredth]

lemma nextColumnNorm_ne_zero (hb : L.β k ≠ 0) : L.nextColumnNorm ≠ 0 :=
  ne_of_gt (L.nextColumnNorm_pos hb)




noncomputable def normalizedVNext : Vec n :=
  if hb : L.β k ≠ 0 then
    (L.nextColumnNorm)⁻¹ • L.v (k + 1)
  else fun i => L.normalizedV i ⟨0, L.hk_pos⟩


noncomputable def normalizedBeta : ℝ :=
  if _hb : L.β k ≠ 0 then
    L.β k * L.nextColumnNorm *
      (L.columnNorm (lastIndex L.hk_pos))⁻¹
  else 0

theorem normalizedVNext_unit : vnorm L.normalizedVNext = 1 := by
  unfold normalizedVNext
  split_ifs with hb
  · rw [vnorm_smul, abs_of_nonneg (inv_nonneg.mpr
      (L.nextColumnNorm_pos hb).le)]
    exact inv_mul_cancel₀ (L.nextColumnNorm_ne_zero hb)
  · simpa using L.normalizedV_unit ⟨0, L.hk_pos⟩

lemma normalizedBeta_nonneg : 0 ≤ L.normalizedBeta := by
  unfold normalizedBeta
  split_ifs with hb
  · exact mul_nonneg
      (mul_nonneg (L.hβ_nonneg k le_rfl) (vnorm_nonneg _))
      (L.invColumnNorm_nonneg _)
  · exact le_rfl

lemma lastIndex_succ : (lastIndex L.hk_pos).1 + 1 = k := by
  have hk := L.hk_pos
  change k - 1 + 1 = k
  omega


theorem boundary_eq_lastOuter :
    L.boundary = lastOuter L.hk_pos L.rawBoundary := by
  ext i j
  by_cases hlt : j.1 + 1 < k
  · have hj : j ≠ lastIndex L.hk_pos := by
      intro h
      subst j
      change k - 1 + 1 < k at hlt
      omega
    have hcoord : lastCoord L.hk_pos j = 0 := by
      simp only [lastCoord]
      apply Pi.single_eq_of_ne
      intro h
      apply hj
      apply Fin.ext
      simpa [lastIndex] using congrArg Fin.val h
    simp [boundary, hlt, lastOuter, Matrix.vecMulVec, hcoord]
  · have hj : j = lastIndex L.hk_pos := by
      apply Fin.ext
      change j.1 = k - 1
      omega
    subst j
    have hk := L.hk_pos
    have hlast : k - 1 + 1 = k := by omega
    have hnext : k - 1 + 2 = k + 1 := by omega
    have hnot : ¬k - 1 + 1 < k := by omega
    simp [boundary, rawBoundary, lastOuter, Matrix.vecMulVec,
      lastCoord, lastIndex, hlast, hnext, hnot]

lemma lastOuter_mul_invNormDiag (x : Vec n) :
    lastOuter L.hk_pos x * L.invNormDiag =
      (L.columnNorm (lastIndex L.hk_pos))⁻¹ • lastOuter L.hk_pos x := by
  ext i j
  by_cases hj : j = lastIndex L.hk_pos
  · subst j
    simp [lastOuter, Matrix.vecMulVec, lastCoord, lastIndex,
      invNormDiag, mul_comm]
  · have hcoord : lastCoord L.hk_pos j = 0 := by
      simp only [lastCoord]
      apply Pi.single_eq_of_ne
      intro h
      apply hj
      apply Fin.ext
      simpa [lastIndex] using congrArg Fin.val h
    simp [lastOuter, Matrix.vecMulVec, invNormDiag, hcoord]

lemma normalized_boundary_vector :
    L.normalizedBeta • L.normalizedVNext =
      (L.columnNorm (lastIndex L.hk_pos))⁻¹ • L.rawBoundary := by
  unfold normalizedBeta normalizedVNext rawBoundary
  split_ifs with hb
  · ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [L.nextColumnNorm_ne_zero hb]
  · have hb0 : L.β k = 0 := not_ne_iff.mp hb
    simp [hb0]


theorem boundary_mul_invNormDiag :
    L.boundary * L.invNormDiag =
      L.normalizedBeta • lastOuter L.hk_pos L.normalizedVNext := by
  rw [L.boundary_eq_lastOuter, L.lastOuter_mul_invNormDiag]
  rw [← lastOuter_smul]
  rw [← L.normalized_boundary_vector, lastOuter_smul]

end LanczosRun
end FinitePrecisionLanczos
