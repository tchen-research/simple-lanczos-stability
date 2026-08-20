import FinitePrecisionLanczos.Core.DilationRecurrence

/-!
# Explicit bounds for the physical dilation

This file proves the quantitative part of `lem:dilation`.  The
constants are intentionally coarse; unlike `\lesssim_k`, every hidden power
of `k` is visible in the theorem statements.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n k : ℕ}

/-- Squared Euclidean norm of a block stack. -/
lemma coordNorm_stack_mulVec_sq (B : Fin k → Mat n k) (x : Vec k) :
    coordNorm (stackBlocks B *ᵥ x) ^ 2 =
      ∑ r : Fin k, vnorm (B r *ᵥ x) ^ 2 := by
  rw [coordNorm_sq]
  simp only [Matrix.mulVec, stackBlocks, dotProduct, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [vnorm_sq]
  rfl

/-- Dimension-free vertical-stack estimate. -/
theorem norm_stackBlocks_le (hk : 0 < k) (B : Fin k → Mat n k) (R : ℝ)
    (hR : 0 ≤ R) (hB : ∀ r, ‖B r‖ ≤ R) :
    ‖stackBlocks B‖ ≤ (k : ℝ) * R := by
  rw [← norm_indexedMatCLM]
  refine (indexedMatCLM (stackBlocks B)).opNorm_le_bound
    (mul_nonneg (Nat.cast_nonneg _) hR) fun x => ?_
  rw [indexedMatCLM_apply]
  change coordNorm (stackBlocks B *ᵥ WithLp.ofLp x) ≤ (k : ℝ) * R * ‖x‖
  have henergy := coordNorm_stack_mulVec_sq B (WithLp.ofLp x)
  have hterm (r : Fin k) :
      vnorm (B r *ᵥ WithLp.ofLp x) ≤ R * ‖x‖ := by
    calc
      vnorm (B r *ᵥ WithLp.ofLp x) ≤ ‖B r‖ * vnorm (WithLp.ofLp x) :=
        vnorm_mulVec_le _ _
      _ ≤ R * ‖x‖ := by
        exact mul_le_mul_of_nonneg_right (hB r) (norm_nonneg x)
  have hsum :
      (∑ r : Fin k, vnorm (B r *ᵥ WithLp.ofLp x) ^ 2) ≤
        (k : ℝ) * (R * ‖x‖) ^ 2 := by
    calc
      (∑ r : Fin k, vnorm (B r *ᵥ WithLp.ofLp x) ^ 2) ≤
          ∑ _r : Fin k, (R * ‖x‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro r _hr
        nlinarith [hterm r, vnorm_nonneg (B r *ᵥ WithLp.ofLp x),
          mul_nonneg hR (norm_nonneg x)]
      _ = (k : ℝ) * (R * ‖x‖) ^ 2 := by simp
  have hkR : 0 ≤ (k : ℝ) * R * ‖x‖ := by positivity
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq : coordNorm (stackBlocks B *ᵥ WithLp.ofLp x) ^ 2 ≤
      ((k : ℝ) * R * ‖x‖) ^ 2 := by
    rw [henergy]
    nlinarith [mul_nonneg (sq_nonneg (R * ‖x‖)) (sub_nonneg.mpr hk1)]
  nlinarith [coordNorm_nonneg (stackBlocks B *ᵥ WithLp.ofLp x),
    sq_nonneg (coordNorm (stackBlocks B *ᵥ WithLp.ofLp x) +
      ((k : ℝ) * R * ‖x‖))]

lemma norm_pow_le_one (hk : 0 < k) (K : Mat k k) (hK : ‖K‖ ≤ 1)
    (r : ℕ) : ‖K ^ r‖ ≤ 1 := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  calc
    ‖K ^ r‖ ≤ ‖K‖ ^ r := norm_pow_le _ _
    _ ≤ 1 ^ r := pow_le_pow_left₀ (norm_nonneg K) hK r
    _ = 1 := one_pow _

/-- Explicit version of `‖L_r‖ ≤ r ‖L‖` for the iterated exchange
residual. -/
theorem powerResidual_norm (hk : 0 < k) (K L : Mat k k)
    (hK : ‖K‖ ≤ 1) (r : ℕ) :
    ‖powerResidual K L r‖ ≤ (r : ℝ) * ‖L‖ := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  induction r with
  | zero => simp [powerResidual]
  | succ r ih =>
      rw [powerResidual]
      calc
        ‖powerResidual K L r * K + K ^ r * L‖ ≤
            ‖powerResidual K L r * K‖ + ‖K ^ r * L‖ := norm_add_le _ _
        _ ≤ ‖powerResidual K L r‖ * ‖K‖ + ‖K ^ r‖ * ‖L‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ ((r : ℝ) * ‖L‖) * 1 + 1 * ‖L‖ := by
          gcongr
          exact norm_pow_le_one hk K hK r
        _ = ((r + 1 : ℕ) : ℝ) * ‖L‖ := by push_cast; ring

/-- Uniform bound on every block of the propagated error. -/
theorem physicalErrorBlock_norm (hk : 0 < k) (V E0 : Mat n k)
    (C K L : Mat k k) (r : ℕ) (hr : r < k)
    (hV : ‖V‖ ≤ (k : ℝ)) (hC : ‖C‖ ≤ 2) (hK : ‖K‖ ≤ 1) :
    ‖physicalErrorBlock V E0 C K L r‖ ≤
      2 * ‖E0‖ + 2 * (k : ℝ) ^ 2 * ‖L‖ := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  by_cases hr0 : r = 0
  · subst r
    simp only [physicalErrorBlock, ↓reduceIte]
    have hE := norm_nonneg E0
    have hL0 := norm_nonneg L
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) hL0]
  · rw [physicalErrorBlock, if_neg hr0]
    have hKr := norm_pow_le_one hk K hK r
    have hPr := powerResidual_norm hk K L hK r
    have hrk : (r : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt hr)
    have hfirst : ‖E0 * K ^ r‖ ≤ ‖E0‖ * ‖K ^ r‖ := norm_mul_le _ _
    have hsecond : ‖V * C * powerResidual K L r‖ ≤
        (‖V‖ * ‖C‖) * ‖powerResidual K L r‖ := by
      calc
        ‖V * C * powerResidual K L r‖ ≤
            ‖V * C‖ * ‖powerResidual K L r‖ := norm_mul_le _ _
        _ ≤ (‖V‖ * ‖C‖) * ‖powerResidual K L r‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le V C) (norm_nonneg _)
    have hEfin : ‖E0‖ * ‖K ^ r‖ ≤ ‖E0‖ * 1 :=
      mul_le_mul_of_nonneg_left hKr (norm_nonneg E0)
    have hcoeff : ‖V‖ * ‖C‖ ≤ (k : ℝ) * 2 :=
      mul_le_mul hV hC (norm_nonneg C) (Nat.cast_nonneg _)
    have hVCfin : (‖V‖ * ‖C‖) * ‖powerResidual K L r‖ ≤
        ((k : ℝ) * 2) * ((r : ℝ) * ‖L‖) :=
      mul_le_mul hcoeff hPr (norm_nonneg _) (by positivity)
    calc
      ‖E0 * K ^ r + V * C * powerResidual K L r‖ ≤
          ‖E0 * K ^ r‖ + ‖V * C * powerResidual K L r‖ := norm_add_le _ _
      _ ≤ ‖E0‖ * ‖K ^ r‖ + (‖V‖ * ‖C‖) * ‖powerResidual K L r‖ :=
        add_le_add hfirst hsecond
      _ ≤ ‖E0‖ * 1 + (((k : ℝ)) * 2) * ((r : ℝ) * ‖L‖) :=
        add_le_add hEfin hVCfin
      _ ≤ 2 * ‖E0‖ + 2 * (k : ℝ) ^ 2 * ‖L‖ := by
        have hE := norm_nonneg E0
        have hL0 := norm_nonneg L
        have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
        have hprod : 0 ≤ 2 * (k : ℝ) * ((k : ℝ) - r) * ‖L‖ := by
          positivity
        nlinarith

/-- Explicit polynomial representative for the last estimate in
`lem:dilation`. -/
theorem physicalError_norm (hk : 0 < k) (V E0 : Mat n k)
    (C K L : Mat k k)
    (hV : ‖V‖ ≤ (k : ℝ)) (hC : ‖C‖ ≤ 2) (hK : ‖K‖ ≤ 1) :
    ‖physicalError V E0 C K L‖ ≤
      2 * (k : ℝ) * ‖E0‖ + 2 * (k : ℝ) ^ 3 * ‖L‖ := by
  have hR : 0 ≤ 2 * ‖E0‖ + 2 * (k : ℝ) ^ 2 * ‖L‖ := by positivity
  have hs := norm_stackBlocks_le hk
    (fun r : Fin k => physicalErrorBlock V E0 C K L r.1)
    (2 * ‖E0‖ + 2 * (k : ℝ) ^ 2 * ‖L‖) hR
    (fun r => physicalErrorBlock_norm hk V E0 C K L r.1 r.2 hV hC hK)
  change ‖physicalError V E0 C K L‖ ≤ _
  unfold physicalError
  calc
    ‖stackBlocks (fun r : Fin k => physicalErrorBlock V E0 C K L r.1)‖ ≤
        (k : ℝ) * (2 * ‖E0‖ + 2 * (k : ℝ) ^ 2 * ‖L‖) := hs
    _ = 2 * (k : ℝ) * ‖E0‖ + 2 * (k : ℝ) ^ 3 * ‖L‖ := by ring

end FinitePrecisionLanczos
