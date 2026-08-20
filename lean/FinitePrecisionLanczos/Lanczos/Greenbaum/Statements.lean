import FinitePrecisionLanczos.Lanczos.Greenbaum.Dilation

/-!
# Statements matching the split Greenbaum proof

The Greenbaum construction is implemented in small algebraic modules.  This
file packages those results in the three stages now displayed in the PDF:
normalized local errors, the normalized Gram commutator, and the nilpotent
isometry.  Constants suppressed by `\lesssim_k` in the PDF remain
explicit here.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- A normalized adjacent product is the corresponding raw local product,
divided by the two column norms. -/
lemma normalized_adjacent_product_identity (i j : Fin k)
    (hij : i.1 + 1 = j.1) :
    L.β (i.1 + 1) *
        |vdot (fun r => L.normalizedV r i) (fun r => L.normalizedV r j)| =
      (L.columnNorm i)⁻¹ * (L.columnNorm j)⁻¹ * |L.p (i.1 + 1)| := by
  rw [L.normalizedV_column i, L.normalizedV_column j]
  simp only [vdot, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [show L.v (j.1 + 1) = L.v (i.1 + 2) by rw [← hij]]
  rw [p]
  simp only [vdot, dotProduct_smul, smul_eq_mul, abs_mul]
  rw [abs_of_nonneg (L.hβ_nonneg (i.1 + 1) (by omega)),
    abs_of_nonneg (L.invColumnNorm_nonneg i),
    abs_of_nonneg (L.invColumnNorm_nonneg j)]
  ring

/-- Explicit adjacent-product estimate in `lem:normalized-errors`. -/
theorem normalized_adjacent_product_bound (i j : Fin k)
    (hij : i.1 + 1 = j.1) :
    L.β (i.1 + 1) *
        |vdot (fun r => L.normalizedV r i) (fun r => L.normalizedV r j)| ≤
      (4800 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  rw [L.normalized_adjacent_product_identity i j hij]
  have hp := L.local_product_bound (i.1 + 1) (by omega)
    (show i.1 + 1 ≤ k by omega)
  have hi := L.invColumnNorm_le_two i
  have hj := L.invColumnNorm_le_two j
  have hi0 := L.invColumnNorm_nonneg i
  have hj0 := L.invColumnNorm_nonneg j
  have hp0 : 0 ≤ |L.p (i.1 + 1)| := abs_nonneg _
  calc
    (L.columnNorm i)⁻¹ * (L.columnNorm j)⁻¹ * |L.p (i.1 + 1)|
        ≤ 2 * 2 * ((1200 * ((i.1 + 1 : ℕ) : ℝ)) * L.ε * ‖L.H‖) := by
          gcongr
    _ ≤ (4800 * (k : ℝ)) * L.ε * ‖L.H‖ := by
      have hik : ((i.1 + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show i.1 + 1 ≤ k by omega)
      have hs : 0 ≤ L.ε * ‖L.H‖ :=
        mul_nonneg L.hε_nonneg (norm_nonneg _)
      nlinarith

/-- The normalized boundary product is the last raw local product divided by
the square of the last computed column norm. -/
lemma normalized_boundary_product_identity :
    L.normalizedBeta *
        |vdot (fun r => L.normalizedV r (lastIndex L.hk_pos)) L.normalizedVNext| =
      (L.columnNorm (lastIndex L.hk_pos))⁻¹ ^ 2 * |L.p k| := by
  have hb := L.normalized_boundary_vector
  have hcol := L.normalizedV_column (lastIndex L.hk_pos)
  have hlast := L.lastIndex_succ
  rw [← abs_of_nonneg L.normalizedBeta_nonneg, ← abs_mul]
  have hdot :
      L.normalizedBeta *
          vdot (fun r => L.normalizedV r (lastIndex L.hk_pos)) L.normalizedVNext =
        vdot (fun r => L.normalizedV r (lastIndex L.hk_pos))
          (L.normalizedBeta • L.normalizedVNext) := by
    simp [vdot, dotProduct_smul, smul_eq_mul]
  rw [hdot]
  rw [hb, hcol]
  simp only [vdot, smul_dotProduct, dotProduct_smul, smul_eq_mul, abs_mul]
  rw [p, rawBoundary, hlast]
  simp only [vdot, dotProduct_smul, smul_eq_mul, abs_mul]
  rw [abs_of_nonneg (L.hβ_nonneg k le_rfl),
    abs_of_nonneg (L.invColumnNorm_nonneg (lastIndex L.hk_pos))]
  ring

/-- Explicit boundary-product estimate in `lem:normalized-errors`. -/
theorem normalized_boundary_product_bound :
    L.normalizedBeta *
        |vdot (fun r => L.normalizedV r (lastIndex L.hk_pos)) L.normalizedVNext| ≤
      (4800 * (k : ℝ)) * L.ε * ‖L.H‖ := by
  rw [L.normalized_boundary_product_identity]
  have hp := L.local_product_bound k (Nat.succ_le_iff.mpr L.hk_pos) le_rfl
  have hd := L.invColumnNorm_le_two (lastIndex L.hk_pos)
  have hd0 := L.invColumnNorm_nonneg (lastIndex L.hk_pos)
  have hs : 0 ≤ L.ε * ‖L.H‖ :=
    mul_nonneg L.hε_nonneg (norm_nonneg _)
  calc
    (L.columnNorm (lastIndex L.hk_pos))⁻¹ ^ 2 * |L.p k|
        ≤ 2 ^ 2 * ((1200 * (k : ℝ)) * L.ε * ‖L.H‖) := by
          gcongr
    _ = (4800 * (k : ℝ)) * L.ε * ‖L.H‖ := by ring

/-- Explicit-constant form of `lem:normalized-errors`. -/
structure NormalizedLocalErrors : Prop where
  residual : ‖L.normalizedE‖ ≤ (2600 * (k : ℝ) ^ 4) * L.ε * ‖L.H‖
  adjacent : ∀ i j : Fin k, i.1 + 1 = j.1 →
    L.β (i.1 + 1) *
        |vdot (fun r => L.normalizedV r i) (fun r => L.normalizedV r j)| ≤
      (4800 * (k : ℝ)) * L.ε * ‖L.H‖
  boundary :
    L.normalizedBeta *
        |vdot (fun r => L.normalizedV r (lastIndex L.hk_pos)) L.normalizedVNext| ≤
      (4800 * (k : ℝ)) * L.ε * ‖L.H‖

/-- `lem:normalized-errors`, in the order printed in the PDF. -/
theorem normalized_local_errors : L.NormalizedLocalErrors := by
  exact {
    residual := L.normalizedE_bound
    adjacent := L.normalized_adjacent_product_bound
    boundary := L.normalized_boundary_product_bound
  }

/-! ## The normalized Gram commutator -/

/-- Tridiagonality of `T_k`, strict upper triangularity of `U`, and the
last-column support of the boundary term make the normalized commutator
upper triangular. -/
theorem normalizedCommutator_upper : Upper L.normalizedCommutator := by
  intro i j hji
  have hTU : (L.Tmat * L.normalizedU) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro m _hm
    by_cases hmj : m.1 < j.1
    · have him : i ≠ m := by intro h; subst m; omega
      have hforward : ¬i.1 + 1 = m.1 := by omega
      have hbackward : ¬m.1 + 1 = i.1 := by omega
      rw [show L.Tmat i m = 0 by
        simp [Tmat, him, hforward, hbackward]]
      simp
    · rw [L.normalizedU_strictUpper m j hmj]
      simp
  have hUT : (L.normalizedU * L.Tmat) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro m _hm
    by_cases him : i.1 < m.1
    · have hmj : m ≠ j := by intro h; subst m; omega
      have hforward : ¬m.1 + 1 = j.1 := by omega
      have hbackward : ¬j.1 + 1 = m.1 := by omega
      rw [show L.Tmat m j = 0 by
        simp [Tmat, hmj, hforward, hbackward]]
      simp
    · rw [L.normalizedU_strictUpper i m him]
      simp
  have hjlast : j ≠ lastIndex L.hk_pos := by
    intro h
    subst j
    have hi := i.2
    change k - 1 < i.1 at hji
    omega
  have hcoord : lastCoord L.hk_pos j = 0 := by
    simp only [lastCoord]
    apply Pi.single_eq_of_ne
    intro h
    apply hjlast
    apply Fin.ext
    simpa [lastIndex] using congrArg Fin.val h
  rw [normalizedCommutator, Matrix.sub_apply, Matrix.sub_apply, hTU, hUT]
  simp [lastOuter, Matrix.vecMulVec, hcoord]

/-- The exact skew identity `eq:normalized-commutator`. -/
theorem normalized_commutator_skew :
    L.normalizedCommutator - L.normalizedCommutatorᵀ =
      L.normalizedVᵀ * L.normalizedE - L.normalizedEᵀ * L.normalizedV := by
  let G : Mat k k := L.normalizedVᵀ * L.normalizedV
  let B : Mat k k :=
    L.normalizedBeta • lastOuter L.hk_pos L.normalizedA
  let Z : Mat k k := L.normalizedVᵀ * L.normalizedE
  have hprojected :
      L.normalizedVᵀ * L.H * L.normalizedV = G * L.Tmat + B + Z := by
    have h := congrArg (fun A : Mat n k => L.normalizedVᵀ * A)
      L.normalized_governing
    simpa [G, B, Z, Matrix.mul_add, Matrix.mul_smul, mul_lastOuter,
      normalizedA, Matrix.mul_assoc] using h
  have hleftSymm :
      (L.normalizedVᵀ * L.H * L.normalizedV)ᵀ =
        L.normalizedVᵀ * L.H * L.normalizedV := by
    simp [Matrix.transpose_mul, L.hHsymm, Matrix.mul_assoc]
  have hbalance :
      G * L.Tmat + B + Z =
        L.Tmat * G + Bᵀ + Zᵀ := by
    calc
      G * L.Tmat + B + Z =
          L.normalizedVᵀ * L.H * L.normalizedV := hprojected.symm
      _ = (L.normalizedVᵀ * L.H * L.normalizedV)ᵀ := hleftSymm.symm
      _ = (G * L.Tmat + B + Z)ᵀ := by rw [hprojected]
      _ = L.Tmat * G + Bᵀ + Zᵀ := by
        simp [Matrix.transpose_add, Matrix.transpose_mul, L.Tmat_transpose,
          G, Matrix.mul_assoc]
  have hright :
      L.Tmat * G + Bᵀ = G * L.Tmat + B + Z - Zᵀ := by
    calc
      L.Tmat * G + Bᵀ = (L.Tmat * G + Bᵀ + Zᵀ) - Zᵀ := by
        noncomm_ring
      _ = (G * L.Tmat + B + Z) - Zᵀ := by rw [← hbalance]
  have hG : G = 1 + L.normalizedU + L.normalizedUᵀ := by
    exact L.normalized_gram_split
  calc
    L.normalizedCommutator - L.normalizedCommutatorᵀ =
        (L.Tmat * G + Bᵀ) - (G * L.Tmat + B) := by
      simp only [normalizedCommutator, Matrix.transpose_sub,
        Matrix.transpose_mul, L.Tmat_transpose, Matrix.transpose_smul]
      rw [hG]
      simp only [B]
      noncomm_ring
    _ = Z - Zᵀ := by rw [hright]; noncomm_ring
    _ = L.normalizedVᵀ * L.normalizedE -
        L.normalizedEᵀ * L.normalizedV := by
      simp [Z, Matrix.transpose_mul]

/-- Explicit-constant form of `lem:normalized-commutator`. -/
structure NormalizedGramCommutator : Prop where
  upper : Upper L.normalizedCommutator
  skew_identity :
    L.normalizedCommutator - L.normalizedCommutatorᵀ =
      L.normalizedVᵀ * L.normalizedE - L.normalizedEᵀ * L.normalizedV
  norm_bound : ‖L.normalizedCommutator‖ ≤
    (50000 * (k : ℝ) ^ 5) * L.ε * ‖L.H‖

/-- `lem:normalized-commutator`, including both conclusions. -/
theorem normalized_gram_commutator : L.NormalizedGramCommutator := by
  exact {
    upper := L.normalizedCommutator_upper
    skew_identity := L.normalized_commutator_skew
    norm_bound := L.normalizedCommutator_bound
  }

/-! ## The nilpotent isometry -/

/-- `K` is strictly upper triangular, the first conclusion of
`lem:isometry`. -/
theorem greenbaumK_strictUpper : StrictUpper L.greenbaumK := by
  exact triangularK_strictUpper L.hk_pos L.normalizedU
    L.normalizedU_strictUpper

/-- First displayed identity in `lem:isometry`. -/
theorem greenbaum_recombined_gram :
    (L.normalizedV * L.greenbaumC)ᵀ *
        (L.normalizedV * L.greenbaumC) =
      1 - L.greenbaumKᵀ * L.greenbaumK := by
  simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using
    L.greenbaum_isometry_identity

/-- Second displayed identity in `lem:isometry`. -/
theorem greenbaum_recombined_cross :
    (L.normalizedV * L.greenbaumC)ᵀ *ᵥ L.greenbaumY =
      -(L.greenbaumKᵀ *ᵥ L.greenbaumS) := by
  have h := L.greenbaum_one_step_cross
  have hrewrite :
      L.greenbaumCᵀ *ᵥ (L.normalizedVᵀ *ᵥ L.greenbaumY) =
        (L.normalizedV * L.greenbaumC)ᵀ *ᵥ L.greenbaumY := by
    simp only [Matrix.transpose_mul, Matrix.mulVec_mulVec]
  rw [hrewrite] at h
  apply eq_neg_of_add_eq_zero_left
  simpa only [add_comm] using h

/-- Third displayed identity in `lem:isometry`. -/
theorem greenbaum_recombined_norm :
    vnorm L.greenbaumS ^ 2 + vnorm L.greenbaumY ^ 2 = 1 := by
  rw [vnorm_sq, vnorm_sq]
  simpa only [add_comm] using L.greenbaum_one_step_norm

/-- Explicit-constant form of `lem:isometry`, with the three identities
displayed in the current PDF. -/
structure NilpotentIsometry : Prop where
  strict_upper : StrictUpper L.greenbaumK
  nilpotent : L.greenbaumK ^ k = 0
  K_norm : ‖L.greenbaumK‖ ≤ 1
  C_norm : ‖L.greenbaumC‖ ≤ 2
  gram_identity :
    (L.normalizedV * L.greenbaumC)ᵀ *
        (L.normalizedV * L.greenbaumC) =
      1 - L.greenbaumKᵀ * L.greenbaumK
  cross_identity :
    (L.normalizedV * L.greenbaumC)ᵀ *ᵥ L.greenbaumY =
      -(L.greenbaumKᵀ *ᵥ L.greenbaumS)
  norm_identity : vnorm L.greenbaumS ^ 2 + vnorm L.greenbaumY ^ 2 = 1

/-- `lem:isometry`, in the order of its conclusions in the PDF. -/
theorem nilpotent_isometry : L.NilpotentIsometry := by
  exact {
    strict_upper := L.greenbaumK_strictUpper
    nilpotent := L.greenbaumK_nilpotent
    K_norm := L.greenbaumK_norm_le_one
    C_norm := L.greenbaumC_norm_le_two
    gram_identity := L.greenbaum_recombined_gram
    cross_identity := L.greenbaum_recombined_cross
    norm_identity := L.greenbaum_recombined_norm
  }

/-! ## The assembled physical dilation -/

/-- Explicit-constant form of `eq:block-recurrence` for one physical block. -/
structure BlockRecurrence (r : ℕ) (hr : r < k) : Prop where
  equation :
    L.H * L.greenbaumVBlock r =
      L.greenbaumVBlock r * L.Tmat +
        L.normalizedBeta • lastOuter L.hk_pos (L.greenbaumBoundaryBlock r) +
        L.greenbaumErrorBlock r
  error_bound :
    ‖L.greenbaumErrorBlock r‖ ≤
      (1000000 * (k : ℝ) ^ 7) * L.ε * ‖L.H‖

/-- `eq:block-recurrence`, including its residual estimate. -/
theorem block_recurrence (r : ℕ) (hr : r < k) :
    L.BlockRecurrence r hr := by
  exact {
    equation := L.greenbaum_block_recurrence r
    error_bound := L.greenbaumErrorBlock_bound r hr
  }

/-- Explicit-constant form of all conclusions in `lem:dilation`.  The PDF
states existence; Lean records the concrete witnesses constructed in
`GreenbaumDilation`. -/
structure PhysicalDilation : Prop where
  boundary_nonnegative : 0 ≤ L.normalizedBeta
  Vhat_orthonormal : L.greenbaumXᵀ * L.greenbaumX = 1
  Vhat_orthogonal_vhat : L.greenbaumXᵀ *ᵥ L.greenbaumP = 0
  vhat_norm : coordNorm L.greenbaumP ≤ 1
  first_column :
    L.greenbaumX *ᵥ firstCoord L.hk_pos =
      physicalFirst L.hk_pos L.normalizedV
  recurrence :
    L.greenbaumBlockOperator * L.greenbaumX =
      L.greenbaumX * L.Tmat +
        L.normalizedBeta • lastOuter L.hk_pos L.greenbaumP + L.greenbaumError
  error_bound :
    ‖L.greenbaumError‖ ≤
      (1000000 * (k : ℝ) ^ 8) * L.ε * ‖L.H‖

/-- `lem:dilation`, with the constructed witnesses rather than an
existential wrapper. -/
theorem physical_dilation : L.PhysicalDilation := by
  exact {
    boundary_nonnegative := L.normalizedBeta_nonneg
    Vhat_orthonormal := L.greenbaumX_orthonormal
    Vhat_orthogonal_vhat := L.greenbaumX_transpose_mul_P
    vhat_norm := L.greenbaumP_norm_le_one
    first_column := L.greenbaumX_first
    recurrence := L.greenbaum_dilation_recurrence
    error_bound := L.greenbaumError_bound
  }

end LanczosRun
end FinitePrecisionLanczos
