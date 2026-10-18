import FinitePrecisionLanczos.Core.DilationRecurrence


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n k : ℕ}

lemma coordNorm_stack_mulVec_sq {p : ℕ} (B : Fin p → Mat n k) (x : Vec k) :
    coordNorm (stackBlocks B *ᵥ x) ^ 2 =
      ∑ r : Fin p, vnorm (B r *ᵥ x) ^ 2 := by
  rw [coordNorm_sq]
  simp only [Matrix.mulVec, stackBlocks, dotProduct, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [vnorm_sq]
  rfl

/-- Stacking p blocks costs √p, as in the paper. -/
theorem norm_stackBlocks_le_sqrt {p : ℕ} (B : Fin p → Mat n k) (R : ℝ)
    (hR : 0 ≤ R) (hB : ∀ r, ‖B r‖ ≤ R) :
    ‖stackBlocks B‖ ≤ Real.sqrt (p : ℝ) * R := by
  rw [← norm_indexedMatCLM]
  refine (indexedMatCLM (stackBlocks B)).opNorm_le_bound
    (mul_nonneg (Real.sqrt_nonneg _) hR) fun x => ?_
  rw [indexedMatCLM_apply]
  change coordNorm (stackBlocks B *ᵥ WithLp.ofLp x) ≤ Real.sqrt (p : ℝ) * R * ‖x‖
  have henergy := coordNorm_stack_mulVec_sq B (WithLp.ofLp x)
  have hterm (r : Fin p) :
      vnorm (B r *ᵥ WithLp.ofLp x) ≤ R * ‖x‖ := by
    calc
      vnorm (B r *ᵥ WithLp.ofLp x) ≤ ‖B r‖ * vnorm (WithLp.ofLp x) :=
        vnorm_mulVec_le _ _
      _ ≤ R * ‖x‖ := by
        exact mul_le_mul_of_nonneg_right (hB r) (norm_nonneg x)
  have hsum :
      (∑ r : Fin p, vnorm (B r *ᵥ WithLp.ofLp x) ^ 2) ≤
        (p : ℝ) * (R * ‖x‖) ^ 2 := by
    calc
      (∑ r : Fin p, vnorm (B r *ᵥ WithLp.ofLp x) ^ 2) ≤
          ∑ _r : Fin p, (R * ‖x‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro r _hr
        nlinarith [hterm r, vnorm_nonneg (B r *ᵥ WithLp.ofLp x),
          mul_nonneg hR (norm_nonneg x)]
      _ = (p : ℝ) * (R * ‖x‖) ^ 2 := by simp
  have hs : (Real.sqrt (p : ℝ)) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  have hsq : coordNorm (stackBlocks B *ᵥ WithLp.ofLp x) ^ 2 ≤
      (Real.sqrt (p : ℝ) * R * ‖x‖) ^ 2 := by
    rw [henergy]
    nlinarith [hs]
  have hr : 0 ≤ Real.sqrt (p : ℝ) * R * ‖x‖ := by positivity
  nlinarith [coordNorm_nonneg (stackBlocks B *ᵥ WithLp.ofLp x)]

/-- Retained polynomial envelope, derived from the sharper stacking estimate. -/
theorem norm_stackBlocks_le {p : ℕ} (hp : 0 < p) (B : Fin p → Mat n k) (R : ℝ)
    (hR : 0 ≤ R) (hB : ∀ r, ‖B r‖ ≤ R) :
    ‖stackBlocks B‖ ≤ (p : ℝ) * R := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs : Real.sqrt (p : ℝ) ≤ p := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p : ℝ)]
  exact (norm_stackBlocks_le_sqrt B R hR hB).trans (mul_le_mul_of_nonneg_right hs hR)

lemma norm_pow_le_one (hk : 0 < k) (K : Mat k k) (hK : ‖K‖ ≤ 1)
    (r : ℕ) : ‖K ^ r‖ ≤ 1 := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  calc
    ‖K ^ r‖ ≤ ‖K‖ ^ r := norm_pow_le _ _
    _ ≤ 1 ^ r := pow_le_pow_left₀ (norm_nonneg K) hK r
    _ = 1 := one_pow _

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

theorem physicalErrorBlock_norm_le (hk : 0 < k) (V F : Mat n k)
    (C K : Mat k k) (D : ℕ → Mat k k) (ℓ : ℝ) (r : ℕ) (hC : ‖C‖ ≤ 2) (hK : ‖K‖ ≤ 1)
    (hD : ∀ r : ℕ, ‖D r‖ ≤ (r : ℝ) * ℓ) :
    ‖physicalErrorBlock V F C K D r‖ ≤
      2 * ‖F‖ + (2 * (r : ℝ) + 1) * ‖V‖ * ℓ := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have hKr := norm_pow_le_one hk K hK r
  have hDr := hD r
  have hDr' := hD (r + 1)
  have hF : ‖F * C * K ^ r‖ ≤ 2 * ‖F‖ := by
    calc
      ‖F * C * K ^ r‖ ≤ ‖F‖ * ‖C‖ * ‖K ^ r‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖F‖ * 2 * 1 := by gcongr
      _ = 2 * ‖F‖ := by ring
  have hVD : ‖V * (D r - D (r + 1))‖ ≤ (2 * (r : ℝ) + 1) * ‖V‖ * ℓ := by
    calc
      ‖V * (D r - D (r + 1))‖ ≤ ‖V‖ * (‖D r‖ + ‖D (r + 1)‖) :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
      _ ≤ ‖V‖ * ((r : ℝ) * ℓ + ((r + 1 : ℕ) : ℝ) * ℓ) := by gcongr
      _ = (2 * (r : ℝ) + 1) * ‖V‖ * ℓ := by push_cast; ring
  calc
    ‖physicalErrorBlock V F C K D r‖ ≤ ‖F * C * K ^ r‖ + ‖V * (D r - D (r + 1))‖ := by
      rw [physicalErrorBlock]; exact norm_add_le _ _
    _ ≤ 2 * ‖F‖ + (2 * (r : ℝ) + 1) * ‖V‖ * ℓ := add_le_add hF hVD

theorem physicalErrorBlock_norm (hk : 0 < k) (V F : Mat n k)
    (C K : Mat k k) (D : ℕ → Mat k k) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (r : ℕ) (hr : r ≤ k)
    (hV : ‖V‖ ≤ (k : ℝ)) (hC : ‖C‖ ≤ 2) (hK : ‖K‖ ≤ 1)
    (hD : ∀ r : ℕ, ‖D r‖ ≤ (r : ℝ) * ℓ) :
    ‖physicalErrorBlock V F C K D r‖ ≤
      2 * ‖F‖ + (2 * (k : ℝ) + 1) * (k : ℝ) * ℓ := by
  have h := physicalErrorBlock_norm_le hk V F C K D ℓ r hC hK hD
  have hrk : (r : ℝ) ≤ k := by exact_mod_cast hr
  have hcoef : (2 * (r : ℝ) + 1) * ‖V‖ ≤ (2 * (k : ℝ) + 1) * (k : ℝ) :=
    mul_le_mul (by linarith) hV (norm_nonneg _) (by positivity)
  have := mul_le_mul_of_nonneg_right hcoef hℓ
  linarith

end FinitePrecisionLanczos
