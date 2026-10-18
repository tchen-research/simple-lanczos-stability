import FinitePrecisionLanczos.Core.GramCommutator


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n k : ℕ}


def underlineT (T : Mat k k) (β : ℝ) : Mat (k + 1) k :=
  fun i j => if h : i.1 < k then T ⟨i.1, h⟩ j else if j.1 + 1 = k then β else 0

def leadCols {ι : Type*} (W : Matrix ι (Fin (k + 1)) ℝ) : Matrix ι (Fin k) ℝ :=
  fun a j => W a j.castSucc

def lastCol {ι : Type*} (W : Matrix ι (Fin (k + 1)) ℝ) : ι → ℝ :=
  fun a => W a (Fin.last k)

def leadBlock (X : Mat (k + 1) (k + 1)) : Mat k k :=
  fun i j => X i.castSucc j.castSucc

def topRows {κ : Type*} (X : Matrix (Fin (k + 1)) κ ℝ) : Matrix (Fin k) κ ℝ :=
  fun i j => X i.castSucc j

def padRow {κ : Type*} (N : Matrix (Fin k) κ ℝ) : Matrix (Fin (k + 1)) κ ℝ :=
  fun i j => if h : i.1 < k then N ⟨i.1, h⟩ j else 0

def strictUpperPart {m : ℕ} (G : Mat m m) : Mat m m :=
  fun i j => if i.1 < j.1 then G i j else 0


@[simp] lemma underlineT_castSucc (T : Mat k k) (β : ℝ) (i j : Fin k) :
    underlineT T β i.castSucc j = T i j := by
  simp [underlineT]

@[simp] lemma underlineT_last (T : Mat k k) (β : ℝ) (j : Fin k) :
    underlineT T β (Fin.last k) j = if j.1 + 1 = k then β else 0 := by
  simp [underlineT]

lemma underlineT_succ_self (T : Mat k k) (β : ℝ) (i : Fin k) :
    underlineT T β i.succ i =
      if h : i.1 + 1 < k then T ⟨i.1 + 1, h⟩ i else β := by
  by_cases h : i.1 + 1 < k
  · simp [underlineT, h]
  · have h' : i.1 + 1 = k := by omega
    simp [underlineT, h']

@[simp] lemma padRow_castSucc {κ : Type*} (N : Matrix (Fin k) κ ℝ) (i : Fin k) (j : κ) :
    padRow N i.castSucc j = N i j := by
  simp [padRow]

@[simp] lemma padRow_last {κ : Type*} (N : Matrix (Fin k) κ ℝ) (j : κ) :
    padRow N (Fin.last k) j = 0 := by
  simp [padRow]

@[simp] lemma padRow_sub {κ : Type*} (N N' : Matrix (Fin k) κ ℝ) :
    padRow (N - N') = padRow N - padRow N' := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

@[simp] lemma padRow_add {κ : Type*} (N N' : Matrix (Fin k) κ ℝ) :
    padRow (N + N') = padRow N + padRow N' := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

@[simp] lemma padRow_zero {κ : Type*} : padRow (0 : Matrix (Fin k) κ ℝ) = 0 := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp


theorem mul_underlineT {ι : Type*} (hk : 0 < k) (W : Matrix ι (Fin (k + 1)) ℝ)
    (T : Mat k k) (β : ℝ) :
    W * underlineT T β = leadCols W * T + β • lastOuter hk (lastCol W) := by
  ext a j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [underlineT_castSucc, underlineT_last, Matrix.add_apply, Matrix.smul_apply,
    lastOuter_apply, Matrix.mul_apply, leadCols, lastCol, smul_eq_mul]
  split_ifs <;> ring

theorem mul_padRow {ι κ : Type*} [Fintype κ] (W : Matrix ι (Fin (k + 1)) ℝ)
    (N : Matrix (Fin k) κ ℝ) : W * padRow N = leadCols W * N := by
  ext a j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp [Matrix.mul_apply, leadCols]

theorem padRow_mul {m : ℕ} {κ : Type*} (N : Matrix (Fin k) (Fin m) ℝ)
    (Z : Matrix (Fin m) κ ℝ) : padRow N * Z = padRow (N * Z) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply]

theorem upper_mul_padRow {κ : Type*} (X : Mat (k + 1) (k + 1)) (hX : Upper X)
    (N : Matrix (Fin k) κ ℝ) : X * padRow N = padRow (leadBlock X * N) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [padRow_castSucc, padRow_last, mul_zero, add_zero]
    apply Finset.sum_eq_zero
    intro m _
    rw [hX _ _ (by simp), zero_mul]
  · simp [Matrix.mul_apply, leadBlock]

theorem leadBlock_mul (X Y : Mat (k + 1) (k + 1)) (hY : Upper Y) :
    leadBlock (X * Y) = leadBlock X * leadBlock Y := by
  ext i j
  simp only [leadBlock, Matrix.mul_apply]
  rw [Fin.sum_univ_castSucc, hY _ _ (by simp), mul_zero, add_zero]

theorem leadCols_mul {ι : Type*} (W : Matrix ι (Fin (k + 1)) ℝ)
    (X : Mat (k + 1) (k + 1)) (hX : Upper X) :
    leadCols (W * X) = leadCols W * leadBlock X := by
  ext a j
  simp only [leadCols, leadBlock, Matrix.mul_apply]
  rw [Fin.sum_univ_castSucc, hX _ _ (by simp), mul_zero, add_zero]

@[simp] lemma leadBlock_one : leadBlock (1 : Mat (k + 1) (k + 1)) = 1 := by
  ext i j
  simp [leadBlock, Matrix.one_apply]

@[simp] lemma leadBlock_add (X Y : Mat (k + 1) (k + 1)) :
    leadBlock (X + Y) = leadBlock X + leadBlock Y := rfl

@[simp] lemma leadBlock_sub (X Y : Mat (k + 1) (k + 1)) :
    leadBlock (X - Y) = leadBlock X - leadBlock Y := rfl

lemma Upper.mul {m : ℕ} {A B : Mat m m} (hA : Upper A) (hB : Upper B) :
    Upper (A * B) := by
  intro i j hji
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hli : l.1 < i.1
  · rw [hA i l hli, zero_mul]
  · rw [hB l j (by omega), mul_zero]

lemma Upper.pow {m : ℕ} {A : Mat m m} (hA : Upper A) (r : ℕ) : Upper (A ^ r) := by
  induction r with
  | zero => simpa using (Upper.one : Upper (1 : Mat m m))
  | succ r ih => rw [pow_succ]; exact ih.mul hA

lemma leadBlock_pow (X : Mat (k + 1) (k + 1)) (hX : Upper X) (r : ℕ) :
    leadBlock (X ^ r) = leadBlock X ^ r := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ, leadBlock_mul _ _ hX, ih, pow_succ]

lemma StrictUpper.leadBlock {U : Mat (k + 1) (k + 1)} (hU : StrictUpper U) :
    StrictUpper (leadBlock U) := by
  intro i j hij
  exact hU _ _ (by simpa using hij)

lemma triangularK_upper {m : ℕ} (hm : 0 < m) (U : Mat m m) (hU : StrictUpper U) :
    Upper (triangularK U) :=
  (triangularK_strictUpper hm U hU).upper

theorem leadBlock_triangularC (hk : 0 < k) (U : Mat (k + 1) (k + 1))
    (hU : StrictUpper U) :
    leadBlock (triangularC U) = triangularC (leadBlock U) := by
  have hU' := hU.leadBlock
  have hup : Upper (1 + U) := Upper.one.add hU.upper
  have h1 : leadBlock (triangularC U) * (1 + leadBlock U) = 1 := by
    have h := congrArg leadBlock (triangularC_mul_add_one (Nat.succ_pos k) U hU)
    rwa [leadBlock_mul _ _ hup, leadBlock_add, leadBlock_one] at h
  calc
    leadBlock (triangularC U) =
        leadBlock (triangularC U) * ((1 + leadBlock U) * triangularC (leadBlock U)) := by
      rw [add_one_mul_triangularC hk _ hU', Matrix.mul_one]
    _ = triangularC (leadBlock U) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem leadBlock_triangularK (hk : 0 < k) (U : Mat (k + 1) (k + 1))
    (hU : StrictUpper U) :
    leadBlock (triangularK U) = triangularK (leadBlock U) := by
  rw [triangularK, leadBlock_sub, leadBlock_one, leadBlock_triangularC hk U hU,
    triangularK]


lemma strictUpperPart_strictUpper {m : ℕ} (G : Mat m m) :
    StrictUpper (strictUpperPart G) := by
  intro i j hij
  simp [strictUpperPart, hij]

theorem eq_one_add_strictUpperPart {m : ℕ} (G : Mat m m) (hG : Gᵀ = G)
    (hdiag : ∀ i, G i i = 1) :
    G = 1 + strictUpperPart G + (strictUpperPart G)ᵀ := by
  ext i j
  have hsym : G j i = G i j := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hG i) j
  rcases lt_trichotomy i.1 j.1 with hij | hij | hij
  · have hne : i ≠ j := by intro h; subst j; omega
    simp [strictUpperPart, hij, not_lt_of_ge hij.le, hne]
  · have heq : i = j := Fin.ext hij
    subst j
    simp [strictUpperPart, hdiag]
  · have hne : i ≠ j := by intro h; subst j; omega
    simp [strictUpperPart, hij, not_lt_of_ge hij.le, hne, hsym]

lemma leadBlock_strictUpperPart_gram {ι : Type*} [Fintype ι]
    (W : Matrix ι (Fin (k + 1)) ℝ) :
    leadBlock (strictUpperPart (Wᵀ * W)) =
      strictUpperPart ((leadCols W)ᵀ * leadCols W) := by
  ext i j
  simp [leadBlock, strictUpperPart, leadCols, Matrix.mul_apply]

lemma strictUpperPart_gram_castSucc_last {ι : Type*} [Fintype ι]
    (W : Matrix ι (Fin (k + 1)) ℝ) (i : Fin k) :
    strictUpperPart (Wᵀ * W) i.castSucc (Fin.last k) =
      ((leadCols W)ᵀ *ᵥ lastCol W) i := by
  simp [strictUpperPart, leadCols, lastCol, Matrix.mul_apply, Matrix.mulVec,
    dotProduct]

lemma strictUpperPart_last {m : ℕ} (G : Mat (m + 1) (m + 1)) (j : Fin (m + 1)) :
    strictUpperPart G (Fin.last m) j = 0 := by
  simp only [strictUpperPart, Fin.val_last]
  rw [if_neg (by omega)]


def embedJ : Mat (k + 1) k := padRow (1 : Mat k k)

theorem embedJ_mul {κ : Type*} [Fintype κ] (N : Matrix (Fin k) κ ℝ) :
    embedJ * N = padRow N := by
  rw [embedJ, padRow_mul, Matrix.one_mul]

lemma embedJ_transpose_mul_self :
    (embedJ : Mat (k + 1) k)ᵀ * (embedJ : Mat (k + 1) k) = (1 : Mat k k) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp [embedJ, Matrix.one_apply, eq_comm]

lemma embedJ_transpose_mul {κ : Type*} [Fintype κ] (Y : Matrix (Fin (k + 1)) κ ℝ) :
    (embedJ : Mat (k + 1) k)ᵀ * Y = topRows Y := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp [embedJ, Matrix.one_apply, topRows]

lemma leadBlock_eq_embedJ (X : Mat (k + 1) (k + 1)) :
    leadBlock X = (embedJ : Mat (k + 1) k)ᵀ * X * embedJ := by
  rw [Matrix.mul_assoc, embedJ, mul_padRow, Matrix.mul_one, ← embedJ,
    embedJ_transpose_mul]
  rfl

theorem norm_leadBlock_le (X : Mat (k + 1) (k + 1)) : ‖leadBlock X‖ ≤ ‖X‖ := by
  have hJ : ‖(embedJ : Mat (k + 1) k)‖ ≤ 1 :=
    indexed_norm_le_one_of_gram _ embedJ_transpose_mul_self
  have hJt : ‖(embedJ : Mat (k + 1) k)ᵀ‖ ≤ 1 := by rw [norm_transpose]; exact hJ
  rw [leadBlock_eq_embedJ]
  calc
    ‖(embedJ : Mat (k + 1) k)ᵀ * X * embedJ‖ ≤
        ‖(embedJ : Mat (k + 1) k)ᵀ‖ * ‖X‖ * ‖(embedJ : Mat (k + 1) k)‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖X‖ * 1 := by gcongr
    _ = ‖X‖ := by ring


section Orthonormal

variable {ι : Type*} [Fintype ι] (W : Matrix ι (Fin (k + 1)) ℝ) (hW : Wᵀ * W = 1)
include hW

lemma leadCols_orthonormal : (leadCols W)ᵀ * leadCols W = 1 := by
  ext i j
  have h := congrFun (congrFun hW i.castSucc) j.castSucc
  simpa [leadCols, Matrix.mul_apply, Matrix.one_apply, Fin.castSucc_inj] using h

lemma lastCol_dotProduct_self : lastCol W ⬝ᵥ lastCol W = 1 := by
  have h := congrFun (congrFun hW (Fin.last k)) (Fin.last k)
  simpa [lastCol, Matrix.mul_apply, dotProduct] using h

end Orthonormal

end FinitePrecisionLanczos
