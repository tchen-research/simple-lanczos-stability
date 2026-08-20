import FinitePrecisionLanczos.Lanczos.Greenbaum.NormalizedCommutator

/-!
# Instantiating the nilpotent physical dilation

The generic identities from `Core.Dilation`, `Core.DilationRecurrence`, and
`Core.DilationBounds` are instantiated here with the normalized finite-precision
Lanczos run.  Thus every object in `eq:CKsy` through `lem:dilation` has a
named Lean definition.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

noncomputable def greenbaumC : Mat k k := triangularC L.normalizedU
noncomputable def greenbaumK : Mat k k := triangularK L.normalizedU
noncomputable def greenbaumS : Vec k := L.greenbaumC *ᵥ L.normalizedA
noncomputable def greenbaumY : Vec n :=
  L.normalizedVNext - L.normalizedV *ᵥ L.greenbaumS
noncomputable def greenbaumL : Mat k k :=
  L.greenbaumC * L.normalizedCommutator * L.greenbaumC
noncomputable def greenbaumE0 : Mat n k :=
  L.normalizedE * L.greenbaumC - L.normalizedV * L.greenbaumL

/-- `hat H=I_k\otimes H` in `lem:dilation`. -/
def greenbaumBlockOperator :
    Matrix (Fin k × Fin n) (Fin k × Fin n) ℝ := blockDiagonal L.H

/-- The stacked matrix `\widehat V` in `lem:dilation`. -/
noncomputable def greenbaumX : Matrix (Fin k × Fin n) (Fin k) ℝ :=
  physicalX L.normalizedV L.greenbaumC L.greenbaumK

/-- The stacked boundary vector `\widehat v` in `lem:dilation`. -/
noncomputable def greenbaumP : (Fin k × Fin n) → ℝ :=
  physicalP L.normalizedV L.greenbaumC L.greenbaumK L.greenbaumS L.greenbaumY

/-- The stacked residual in `lem:dilation`. -/
noncomputable def greenbaumError : Matrix (Fin k × Fin n) (Fin k) ℝ :=
  physicalError L.normalizedV L.greenbaumE0 L.greenbaumC
    L.greenbaumK L.greenbaumL

/-- Block `r` of `\widehat V` in `eq:block-recurrence`. -/
noncomputable def greenbaumVBlock (r : ℕ) : Mat n k :=
  L.normalizedV * L.greenbaumC * L.greenbaumK ^ r

/-- Block `r` of `\widehat v` in `eq:block-recurrence`. -/
noncomputable def greenbaumBoundaryBlock (r : ℕ) : Vec n :=
  physicalPBlock L.normalizedV L.greenbaumC L.greenbaumK
    L.greenbaumS L.greenbaumY r

/-- Block `r` of `\widehat E` in `eq:block-recurrence`. -/
noncomputable def greenbaumErrorBlock (r : ℕ) : Mat n k :=
  physicalErrorBlock L.normalizedV L.greenbaumE0 L.greenbaumC
    L.greenbaumK L.greenbaumL r

lemma greenbaum_isometry_identity :
    L.greenbaumCᵀ * (L.normalizedVᵀ * L.normalizedV) * L.greenbaumC =
      1 - L.greenbaumKᵀ * L.greenbaumK := by
  exact triangular_isometry_identity L.hk_pos
    (L.normalizedVᵀ * L.normalizedV) L.normalizedU
    L.normalizedU_strictUpper L.normalized_gram_split

/-- First orthogonality conclusion in `lem:dilation`. -/
theorem greenbaumX_orthonormal : L.greenbaumXᵀ * L.greenbaumX = 1 := by
  exact physicalX_orthonormal L.hk_pos L.normalizedV L.normalizedU
    L.normalizedU_strictUpper L.normalized_gram_split

/-- The first-column conclusion in `lem:dilation`. -/
theorem greenbaumX_first :
    L.greenbaumX *ᵥ firstCoord L.hk_pos = physicalFirst L.hk_pos L.normalizedV := by
  exact physicalX_first L.hk_pos L.normalizedV L.normalizedU
    L.normalizedU_strictUpper

lemma normalizedVNext_dot_self : vdot L.normalizedVNext L.normalizedVNext = 1 := by
  have h := vnorm_sq L.normalizedVNext
  rw [L.normalizedVNext_unit] at h
  simpa using h.symm

lemma greenbaum_one_step_cross :
    L.greenbaumKᵀ *ᵥ L.greenbaumS +
      L.greenbaumCᵀ *ᵥ (L.normalizedVᵀ *ᵥ L.greenbaumY) = 0 := by
  exact one_step_cross L.normalizedV L.greenbaumC L.greenbaumK L.normalizedVNext
    L.greenbaum_isometry_identity (by
      simp [greenbaumC, greenbaumK, triangularK])

lemma greenbaum_one_step_norm :
    vdot L.greenbaumY L.greenbaumY + vdot L.greenbaumS L.greenbaumS = 1 := by
  exact one_step_norm L.normalizedV L.greenbaumC L.greenbaumK L.normalizedVNext
    L.normalizedVNext_dot_self L.greenbaum_isometry_identity (by
      simp [greenbaumC, greenbaumK, triangularK])

lemma greenbaumK_nilpotent : L.greenbaumK ^ k = 0 := by
  exact triangularK_pow_card_eq_zero L.hk_pos L.normalizedU
    L.normalizedU_strictUpper

/-- Second orthogonality conclusion in `lem:dilation`. -/
theorem greenbaumX_transpose_mul_P : L.greenbaumXᵀ *ᵥ L.greenbaumP = 0 := by
  exact physicalX_transpose_mul_p L.hk_pos L.normalizedV L.greenbaumC
    L.greenbaumK L.greenbaumS L.greenbaumY L.greenbaum_isometry_identity
    L.greenbaum_one_step_cross L.greenbaumK_nilpotent

/-- Boundary-vector norm conclusion in `lem:dilation`. -/
theorem greenbaumP_norm_le_one : coordNorm L.greenbaumP ≤ 1 := by
  exact physicalP_norm_le_one L.hk_pos L.normalizedV L.greenbaumC L.greenbaumK
    L.greenbaumS L.greenbaumY L.greenbaum_isometry_identity
    L.greenbaum_one_step_norm

/-- The exact identity in `eq:L-commutator`. -/
theorem greenbaumL_identity :
    L.greenbaumL =
      L.Tmat * L.greenbaumK - L.greenbaumK * L.Tmat -
        L.normalizedBeta • lastOuter L.hk_pos L.greenbaumS := by
  simpa [greenbaumL, greenbaumC, greenbaumK, greenbaumS,
    normalizedCommutator] using
      (transformed_commutator L.hk_pos L.Tmat L.normalizedU
        L.normalizedA L.normalizedBeta L.normalizedU_strictUpper)

/-- The initial error block displayed below `eq:block-recurrence`. -/
theorem greenbaumErrorBlock_zero :
    L.greenbaumErrorBlock 0 =
      L.normalizedE * L.greenbaumC - L.normalizedV * L.greenbaumL := by
  simp [greenbaumErrorBlock, physicalErrorBlock, greenbaumE0]

/-- The residual induction printed after `eq:block-recurrence`. -/
theorem greenbaumErrorBlock_succ (r : ℕ) :
    L.greenbaumErrorBlock (r + 1) =
      L.greenbaumErrorBlock r * L.greenbaumK +
        L.greenbaumVBlock r * L.greenbaumL := by
  exact physicalErrorBlock_succ L.normalizedV L.greenbaumE0
    L.greenbaumC L.greenbaumK L.greenbaumL r

/-- The block boundary convention printed before `eq:block-recurrence`. -/
theorem greenbaumBoundaryBlock_zero :
    L.greenbaumBoundaryBlock 0 = L.greenbaumY := by
  simp [greenbaumBoundaryBlock, physicalPBlock]

theorem greenbaumBoundaryBlock_succ (r : ℕ) :
    L.greenbaumBoundaryBlock (r + 1) =
      L.greenbaumVBlock r *ᵥ L.greenbaumS := by
  simp [greenbaumBoundaryBlock, greenbaumVBlock, physicalPBlock]

/-- The base case of `eq:block-recurrence`. -/
theorem greenbaum_block_recurrence_zero :
    L.H * L.greenbaumVBlock 0 =
      L.greenbaumVBlock 0 * L.Tmat +
        L.normalizedBeta • lastOuter L.hk_pos (L.greenbaumBoundaryBlock 0) +
        L.greenbaumErrorBlock 0 := by
  simpa [greenbaumVBlock, greenbaumBoundaryBlock, greenbaumErrorBlock,
    greenbaumC, greenbaumK, greenbaumS, greenbaumY, greenbaumL, greenbaumE0,
    normalizedCommutator, physicalPBlock, physicalErrorBlock] using
      (VC_recurrence L.hk_pos L.H L.normalizedV L.normalizedE L.Tmat
        L.normalizedU L.normalizedVNext L.normalizedA L.normalizedBeta
        L.normalizedU_strictUpper L.normalized_governing)

/-- The induction step of `eq:block-recurrence`. -/
theorem greenbaum_block_recurrence_succ (r : ℕ) :
    L.H * L.greenbaumVBlock (r + 1) =
      L.greenbaumVBlock (r + 1) * L.Tmat +
        L.normalizedBeta •
          lastOuter L.hk_pos (L.greenbaumBoundaryBlock (r + 1)) +
        L.greenbaumErrorBlock (r + 1) := by
  have hbase := L.greenbaum_block_recurrence_zero
  have hs : (1 + L.normalizedU) *ᵥ L.greenbaumS = L.normalizedA := by
    simp [greenbaumS, greenbaumC, Matrix.mulVec_mulVec,
      add_one_mul_triangularC L.hk_pos L.normalizedU
        L.normalizedU_strictUpper]
  have hstep := propagated_block_succ L.hk_pos L.H L.normalizedV
    L.greenbaumE0 L.Tmat L.normalizedU L.greenbaumS L.greenbaumY
    L.normalizedBeta r L.normalizedU_strictUpper (by
      simpa [greenbaumVBlock, greenbaumBoundaryBlock, greenbaumErrorBlock,
        greenbaumC, greenbaumK, greenbaumS, greenbaumY, greenbaumL,
        greenbaumE0, normalizedCommutator, physicalPBlock,
        physicalErrorBlock] using hbase) (by
      rw [hs]
      exact transformed_commutator L.hk_pos L.Tmat L.normalizedU
        L.normalizedA L.normalizedBeta L.normalizedU_strictUpper)
  rw [hs] at hstep
  simpa [greenbaumVBlock, greenbaumBoundaryBlock, greenbaumErrorBlock,
    greenbaumC, greenbaumK, greenbaumS, greenbaumY, greenbaumL,
    normalizedCommutator, physicalPBlock, physicalErrorBlock] using hstep

/-- The exact per-block recurrence `eq:block-recurrence`. -/
theorem greenbaum_block_recurrence (r : ℕ) :
    L.H * L.greenbaumVBlock r =
      L.greenbaumVBlock r * L.Tmat +
        L.normalizedBeta • lastOuter L.hk_pos (L.greenbaumBoundaryBlock r) +
        L.greenbaumErrorBlock r := by
  cases r with
  | zero => exact L.greenbaum_block_recurrence_zero
  | succ r => exact L.greenbaum_block_recurrence_succ r

/-- Exact recurrence in `lem:dilation` for the actual run. -/
theorem greenbaum_dilation_recurrence :
    L.greenbaumBlockOperator * L.greenbaumX =
      L.greenbaumX * L.Tmat +
        L.normalizedBeta • lastOuter L.hk_pos L.greenbaumP + L.greenbaumError := by
  exact physical_dilation_recurrence L.hk_pos L.H L.normalizedV L.normalizedE
    L.Tmat L.normalizedU L.normalizedVNext L.normalizedA L.normalizedBeta
    L.normalizedU_strictUpper L.normalized_governing

/-- The two triangular-factor bounds in `lem:isometry`. -/
theorem greenbaumK_norm_le_one : ‖L.greenbaumK‖ ≤ 1 := by
  exact triangularK_norm_le_one L.hk_pos L.normalizedV L.greenbaumC
    L.greenbaumK L.greenbaum_isometry_identity

theorem greenbaumC_norm_le_two : ‖L.greenbaumC‖ ≤ 2 := by
  exact triangularC_norm_le_two L.hk_pos L.normalizedU L.normalizedV
    L.greenbaum_isometry_identity

lemma greenbaumL_bound :
    ‖L.greenbaumL‖ ≤ (200000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖ := by
  have hcommScale : 0 ≤ (50000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖ :=
    mul_nonneg
      (mul_nonneg (show 0 ≤ (50000 : ℝ) * (k : ℝ) ^ 5 by positivity)
        L.hε_nonneg)
      (norm_nonneg _)
  calc
    ‖L.greenbaumL‖ ≤
        (‖L.greenbaumC‖ * ‖L.normalizedCommutator‖) * ‖L.greenbaumC‖ := by
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (2 * ((50000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖)) * 2 := by
      exact mul_le_mul
        (mul_le_mul L.greenbaumC_norm_le_two L.normalizedCommutator_bound
          (norm_nonneg _) (by norm_num))
        L.greenbaumC_norm_le_two (norm_nonneg _)
          (mul_nonneg (by norm_num) hcommScale)
    _ = (200000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖ := by ring

lemma greenbaumE0_bound :
    ‖L.greenbaumE0‖ ≤ (205200 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have hk46 : (k : ℝ) ^ 4 ≤ (k : ℝ) ^ 6 := by
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) ^ 4 by positivity)
      (show 0 ≤ (k : ℝ) ^ 2 - 1 by nlinarith [sq_nonneg ((k : ℝ) - 1)])]
  have hscale : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
  calc
    ‖L.greenbaumE0‖ ≤
        ‖L.normalizedE * L.greenbaumC‖ + ‖L.normalizedV * L.greenbaumL‖ :=
      norm_sub_le _ _
    _ ≤ ‖L.normalizedE‖ * ‖L.greenbaumC‖ +
        ‖L.normalizedV‖ * ‖L.greenbaumL‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ((2600 * (k : ℝ) ^ 4) * L.ε * ‖L.H‖) * 2 +
        (k : ℝ) * ((200000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖) := by
      exact add_le_add
        (mul_le_mul L.normalizedE_bound L.greenbaumC_norm_le_two
          (norm_nonneg _)
          (mul_nonneg
            (mul_nonneg (show 0 ≤ (2600 : ℝ) * (k : ℝ) ^ 4 by positivity)
              L.hε_nonneg)
            (norm_nonneg _)))
        (mul_le_mul L.normalizedV_norm L.greenbaumL_bound
          (norm_nonneg _) (Nat.cast_nonneg _))
    _ = (5200 * (k : ℝ) ^ 4 + 200000 * (k : ℝ) ^ 6) *
        (L.ε * ‖L.H‖) := by ring
    _ ≤ (5200 * (k : ℝ) ^ 6 + 200000 * (k : ℝ) ^ 6) *
        (L.ε * ‖L.H‖) := by
      have hcoef : 5200 * (k : ℝ) ^ 4 + 200000 * (k : ℝ) ^ 6 ≤
          5200 * (k : ℝ) ^ 6 + 200000 * (k : ℝ) ^ 6 := by
        simpa [add_comm] using add_le_add_right
          (mul_le_mul_of_nonneg_left hk46 (show 0 ≤ (5200 : ℝ) by norm_num))
          (200000 * (k : ℝ) ^ 6)
      exact mul_le_mul_of_nonneg_right hcoef hscale
    _ = (205200 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ := by ring

/-- Explicit representative of the per-block estimate in
`eq:block-recurrence`. -/
theorem greenbaumErrorBlock_bound (r : ℕ) (hr : r < k) :
    ‖L.greenbaumErrorBlock r‖ ≤
      (1000000 * (k : ℝ) ^ 7) * L.ε * ‖L.H‖ := by
  have hgeneric := physicalErrorBlock_norm L.hk_pos L.normalizedV
    L.greenbaumE0 L.greenbaumC L.greenbaumK L.greenbaumL r hr
    L.normalizedV_norm L.greenbaumC_norm_le_two L.greenbaumK_norm_le_one
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have hscale : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
  have hk67 : (k : ℝ) ^ 6 ≤ (k : ℝ) ^ 7 := by
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) ^ 6 by positivity)
      (show 0 ≤ (k : ℝ) - 1 by linarith)]
  calc
    ‖L.greenbaumErrorBlock r‖ ≤
        2 * ‖L.greenbaumE0‖ + 2 * (k : ℝ) ^ 2 * ‖L.greenbaumL‖ := hgeneric
    _ ≤ 2 * ((205200 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖) +
        2 * (k : ℝ) ^ 2 *
          ((200000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left L.greenbaumE0_bound (by norm_num))
        (mul_le_mul_of_nonneg_left L.greenbaumL_bound (by positivity))
    _ = (410400 * (k : ℝ) ^ 6 + 400000 * (k : ℝ) ^ 7) *
        (L.ε * ‖L.H‖) := by ring
    _ ≤ (410400 * (k : ℝ) ^ 7 + 400000 * (k : ℝ) ^ 7) *
        (L.ε * ‖L.H‖) := by
      have hcoef : 410400 * (k : ℝ) ^ 6 + 400000 * (k : ℝ) ^ 7 ≤
          410400 * (k : ℝ) ^ 7 + 400000 * (k : ℝ) ^ 7 := by
        simpa [add_comm] using add_le_add_right
          (mul_le_mul_of_nonneg_left hk67 (show 0 ≤ (410400 : ℝ) by norm_num))
          (400000 * (k : ℝ) ^ 7)
      exact mul_le_mul_of_nonneg_right hcoef hscale
    _ = (810400 * (k : ℝ) ^ 7) * (L.ε * ‖L.H‖) := by ring
    _ ≤ (1000000 * (k : ℝ) ^ 7) * (L.ε * ‖L.H‖) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num)
          (show 0 ≤ (k : ℝ) ^ 7 by positivity)) hscale
    _ = (1000000 * (k : ℝ) ^ 7) * L.ε * ‖L.H‖ := by ring

/-- Explicit polynomial representative for the residual estimate in
`lem:dilation`. -/
theorem greenbaumError_bound :
    ‖L.greenbaumError‖ ≤ (1000000 * (k : ℝ) ^ 8) * L.ε * ‖L.H‖ := by
  have hgeneric := physicalError_norm L.hk_pos L.normalizedV L.greenbaumE0
    L.greenbaumC L.greenbaumK L.greenbaumL L.normalizedV_norm
    L.greenbaumC_norm_le_two L.greenbaumK_norm_le_one
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.hk_pos
  have hscale : 0 ≤ L.ε * ‖L.H‖ := mul_nonneg L.hε_nonneg (norm_nonneg _)
  have hk78 : (k : ℝ) ^ 7 ≤ (k : ℝ) ^ 8 := by
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) ^ 7 by positivity)
      (show 0 ≤ (k : ℝ) - 1 by linarith)]
  calc
    ‖L.greenbaumError‖ ≤
        2 * (k : ℝ) * ‖L.greenbaumE0‖ +
          2 * (k : ℝ) ^ 3 * ‖L.greenbaumL‖ := hgeneric
    _ ≤ 2 * (k : ℝ) *
          ((205200 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖) +
        2 * (k : ℝ) ^ 3 *
          ((200000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left L.greenbaumE0_bound (by positivity))
        (mul_le_mul_of_nonneg_left L.greenbaumL_bound (by positivity))
    _ = (410400 * (k : ℝ) ^ 7 + 400000 * (k : ℝ) ^ 8) *
        (L.ε * ‖L.H‖) := by ring
    _ ≤ (410400 * (k : ℝ) ^ 8 + 400000 * (k : ℝ) ^ 8) *
        (L.ε * ‖L.H‖) := by
      have hcoef : 410400 * (k : ℝ) ^ 7 + 400000 * (k : ℝ) ^ 8 ≤
          410400 * (k : ℝ) ^ 8 + 400000 * (k : ℝ) ^ 8 := by
        simpa [add_comm] using add_le_add_right
          (mul_le_mul_of_nonneg_left hk78 (show 0 ≤ (410400 : ℝ) by norm_num))
          (400000 * (k : ℝ) ^ 8)
      exact mul_le_mul_of_nonneg_right hcoef hscale
    _ = (810400 * (k : ℝ) ^ 8) * (L.ε * ‖L.H‖) := by ring
    _ ≤ (1000000 * (k : ℝ) ^ 8) * (L.ε * ‖L.H‖) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num)
          (show 0 ≤ (k : ℝ) ^ 8 by positivity)) hscale
    _ = (1000000 * (k : ℝ) ^ 8) * L.ε * ‖L.H‖ := by ring

end LanczosRun
end FinitePrecisionLanczos
