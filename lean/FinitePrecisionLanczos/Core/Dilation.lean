import FinitePrecisionLanczos.Core.Nilpotent


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n k : ℕ}

def matFinSum {m n k : ℕ} (A : Fin k → Mat m n) : Mat m n :=
  fun i j => ∑ r, A r i j

def stackBlocks {p : ℕ} (B : Fin p → Mat n k) :
    Matrix (Fin p × Fin n) (Fin k) ℝ :=
  fun ri j => B ri.1 ri.2 j

theorem stackBlocks_gram {p : ℕ} (B : Fin p → Mat n k) :
    (stackBlocks B)ᵀ * stackBlocks B = matFinSum fun r => (B r)ᵀ * B r := by
  ext i j
  simp [stackBlocks, matFinSum, Matrix.mul_apply, Fintype.sum_prod_type]

lemma dilation_gram_summand (K : Mat k k) (r : ℕ) :
    (K ^ r)ᵀ * (1 - Kᵀ * K) * K ^ r =
      (K ^ r)ᵀ * K ^ r - (K ^ (r + 1))ᵀ * K ^ (r + 1) := by
  have hpow : K ^ (r + 1) = K * K ^ r := by
    simpa [Nat.add_comm] using (pow_succ' K r)
  rw [hpow, Matrix.transpose_mul]
  noncomm_ring


lemma vdot_mulVec_left (A : Mat n k) (x : Vec k) (y : Vec n) :
    vdot (A *ᵥ x) y = vdot x (Aᵀ *ᵥ y) := by
  rw [vdot, vdot, dotProduct_comm]
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  exact dotProduct_comm _ _

lemma vdot_sub_right (x y z : Vec n) :
    vdot x (y - z) = vdot x y - vdot x z := by
  simp only [vdot, dotProduct, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring


def firstCoord (hk : 0 < k) : Vec k := Pi.single ⟨0, hk⟩ 1

lemma triangularC_first (hk : 0 < k) (U : Mat k k) (hU : StrictUpper U) :
    triangularC U *ᵥ firstCoord hk = firstCoord hk := by
  have hUe : U *ᵥ firstCoord hk = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, firstCoord, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Pi.zero_apply]
    exact hU i ⟨0, hk⟩ (Nat.not_lt_zero _)
  have hIe : (1 + U) *ᵥ firstCoord hk = firstCoord hk := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, hUe, add_zero]
  calc
    triangularC U *ᵥ firstCoord hk =
        triangularC U *ᵥ ((1 + U) *ᵥ firstCoord hk) := by rw [hIe]
    _ = (triangularC U * (1 + U)) *ᵥ firstCoord hk :=
      Matrix.mulVec_mulVec _ _ _
    _ = firstCoord hk := by
      rw [triangularC_mul_add_one hk U hU, Matrix.one_mulVec]

lemma triangularK_first (hk : 0 < k) (U : Mat k k) (hU : StrictUpper U) :
    triangularK U *ᵥ firstCoord hk = 0 := by
  rw [triangularK, Matrix.sub_mulVec, Matrix.one_mulVec,
    triangularC_first hk U hU, sub_self]

lemma triangularK_pow_first (hk : 0 < k) (U : Mat k k) (hU : StrictUpper U)
    (r : ℕ) (hr : 0 < r) :
    triangularK U ^ r *ᵥ firstCoord hk = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [pow_succ, ← Matrix.mulVec_mulVec, triangularK_first hk U hU,
    Matrix.mulVec_zero]

def physicalFirst (hk : 0 < k) (V : Mat n k) : (Fin (k + 1) × Fin n) → ℝ :=
  fun ri => if ri.1.1 = 0 then V ri.2 ⟨0, hk⟩ else 0


lemma vdot_gram (M : Mat n k) (x : Vec k) :
    vdot (M *ᵥ x) (M *ᵥ x) = vdot x ((Mᵀ * M) *ᵥ x) := by
  rw [vdot_mulVec_left, Matrix.mulVec_mulVec]

lemma one_step_energy (V : Mat n k) (C K : Mat k k)
    (hIso : Cᵀ * (Vᵀ * V) * C = 1 - Kᵀ * K) (x : Vec k) :
    vnorm (K *ᵥ x) ^ 2 + vnorm ((V * C) *ᵥ x) ^ 2 = vnorm x ^ 2 := by
  rw [vnorm_sq, vnorm_sq, vnorm_sq, vdot_gram, vdot_gram]
  have hVC : (V * C)ᵀ * (V * C) = Cᵀ * (Vᵀ * V) * C := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hVC, hIso, Matrix.sub_mulVec, Matrix.one_mulVec, vdot_sub_right]
  rw [← vdot_gram]
  ring

theorem triangularK_norm_le_one (hk : 0 < k) (V : Mat n k) (C K : Mat k k)
    (hIso : Cᵀ * (Vᵀ * V) * C = 1 - Kᵀ * K) : ‖K‖ ≤ 1 := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [← norm_matCLM]
  refine (matCLM K).opNorm_le_bound (by norm_num) fun x => ?_
  rw [matCLM_apply]
  change vnorm (K *ᵥ WithLp.ofLp x) ≤ 1 * ‖x‖
  have he := one_step_energy V C K hIso (WithLp.ofLp x)
  have hother : 0 ≤ vnorm ((V * C) *ᵥ WithLp.ofLp x) ^ 2 := sq_nonneg _
  have hleft := vnorm_nonneg (K *ᵥ WithLp.ofLp x)
  have hx : vnorm (WithLp.ofLp x) = ‖x‖ := rfl
  rw [hx] at he
  simp only [one_mul]
  by_contra hnot
  have hstrict : ‖x‖ < vnorm (K *ᵥ WithLp.ofLp x) := lt_of_not_ge hnot
  have hsum : 0 < vnorm (K *ᵥ WithLp.ofLp x) + ‖x‖ :=
    add_pos_of_pos_of_nonneg (lt_of_le_of_lt (norm_nonneg x) hstrict) (norm_nonneg x)
  have hprod : 0 <
      (vnorm (K *ᵥ WithLp.ofLp x) - ‖x‖) *
        (vnorm (K *ᵥ WithLp.ofLp x) + ‖x‖) :=
    mul_pos (sub_pos.mpr hstrict) hsum
  nlinarith

theorem triangularC_norm_le_two (hk : 0 < k) (U : Mat k k)
    (V : Mat n k) (hIso :
      (triangularC U)ᵀ * (Vᵀ * V) * triangularC U =
        1 - (triangularK U)ᵀ * triangularK U) :
    ‖triangularC U‖ ≤ 2 := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have hK := triangularK_norm_le_one hk V (triangularC U) (triangularK U) hIso
  calc
    ‖triangularC U‖ = ‖(1 : Mat k k) - triangularK U‖ := by
      congr 1
      dsimp [triangularK]
      module
    _ ≤ ‖(1 : Mat k k)‖ + ‖triangularK U‖ := norm_sub_le _ _
    _ ≤ 2 := by
      rw [norm_one]
      linarith


def dilationStack (p : ℕ) {m : ℕ} (V : Mat n m) (C K : Mat m m) :
    Matrix (Fin p × Fin n) (Fin m) ℝ :=
  stackBlocks fun r : Fin p => V * C * K ^ r.1

theorem dilationStack_orthonormal (p : ℕ) {m : ℕ} (V : Mat n m) (C K : Mat m m)
    (hIso : Cᵀ * (Vᵀ * V) * C = 1 - Kᵀ * K) (hNil : K ^ p = 0) :
    (dilationStack p V C K)ᵀ * dilationStack p V C K = 1 := by
  rw [dilationStack, stackBlocks_gram]
  ext i j
  change (∑ r : Fin p, ((V * C * K ^ r.1)ᵀ * (V * C * K ^ r.1)) i j) =
    (1 : Mat m m) i j
  have hterms :
      (∑ r : Fin p, ((V * C * K ^ r.1)ᵀ * (V * C * K ^ r.1)) i j) =
      ∑ r : Fin p,
        (((K ^ r.1)ᵀ * K ^ r.1) i j -
          ((K ^ (r.1 + 1))ᵀ * K ^ (r.1 + 1)) i j) := by
    apply Finset.sum_congr rfl
    intro r _hr
    have hm : (V * C * K ^ r.1)ᵀ * (V * C * K ^ r.1) =
        (K ^ r.1)ᵀ * (1 - Kᵀ * K) * K ^ r.1 := by
      rw [← hIso]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hm, dilation_gram_summand]
    rfl
  rw [hterms]
  have hconvert := Fin.sum_univ_eq_sum_range
    (fun r : ℕ =>
      ((K ^ r)ᵀ * K ^ r) i j - ((K ^ (r + 1))ᵀ * K ^ (r + 1)) i j) p
  rw [hconvert, Finset.sum_range_sub', pow_zero, Matrix.transpose_one, one_mul, hNil,
    Matrix.transpose_zero, zero_mul]
  exact sub_zero ((1 : Mat m m) i j)

theorem dilationStack_first (p : ℕ) {m : ℕ} (hm : 0 < m) (V : Mat n m)
    (U : Mat m m) (hU : StrictUpper U) :
    dilationStack p V (triangularC U) (triangularK U) *ᵥ firstCoord hm =
      fun ri => if ri.1.1 = 0 then V ri.2 ⟨0, hm⟩ else 0 := by
  ext ri
  rcases ri with ⟨r, i⟩
  change ((V * triangularC U * triangularK U ^ r.1) *ᵥ firstCoord hm) i =
    if r.1 = 0 then V i ⟨0, hm⟩ else 0
  by_cases hr : r.1 = 0
  · rw [if_pos hr, hr, pow_zero, Matrix.mul_one, ← Matrix.mulVec_mulVec,
      triangularC_first hm U hU]
    simp [Matrix.mulVec, firstCoord, Pi.single_apply]
  · rw [if_neg hr, ← Matrix.mulVec_mulVec,
      triangularK_pow_first hm U hU r.1 (Nat.pos_of_ne_zero hr), Matrix.mulVec_zero]
    rfl

end FinitePrecisionLanczos
