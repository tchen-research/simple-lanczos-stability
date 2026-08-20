import FinitePrecisionLanczos.Core.Nilpotent










namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n k : ℕ}



def matFinSum {m n k : ℕ} (A : Fin k → Mat m n) : Mat m n :=
  fun i j => ∑ r, A r i j


def stackBlocks (B : Fin k → Mat n k) : Matrix (Fin k × Fin n) (Fin k) ℝ :=
  fun ri j => B ri.1 ri.2 j


def physicalX (V : Mat n k) (C K : Mat k k) :
    Matrix (Fin k × Fin n) (Fin k) ℝ :=
  stackBlocks fun r => V * C * K ^ r.1


theorem stackBlocks_gram (B : Fin k → Mat n k) :
    (stackBlocks B)ᵀ * stackBlocks B = matFinSum fun r => (B r)ᵀ * B r := by
  ext i j
  simp [stackBlocks, matFinSum, Matrix.mul_apply, Fintype.sum_prod_type]

lemma physicalX_gram_expansion (V : Mat n k) (C K : Mat k k) :
    (physicalX V C K)ᵀ * physicalX V C K =
      matFinSum fun r : Fin k =>
        (K ^ r.1)ᵀ * (Cᵀ * (Vᵀ * V) * C) * K ^ r.1 := by
  rw [physicalX, stackBlocks_gram]
  ext i j
  simp only [matFinSum]
  apply Finset.sum_congr rfl
  intro r _hr
  congr 1
  simp only [Matrix.transpose_mul]
  repeat' rw [Matrix.mul_assoc]



lemma dilation_gram_summand (K : Mat k k) (r : ℕ) :
    (K ^ r)ᵀ * (1 - Kᵀ * K) * K ^ r =
      (K ^ r)ᵀ * K ^ r - (K ^ (r + 1))ᵀ * K ^ (r + 1) := by
  have hpow : K ^ (r + 1) = K * K ^ r := by
    simpa [Nat.add_comm] using (pow_succ' K r)
  rw [hpow, Matrix.transpose_mul]
  noncomm_ring



theorem physicalX_orthonormal (hk : 0 < k) (V : Mat n k) (U : Mat k k)
    (hU : StrictUpper U) (hGram : Vᵀ * V = 1 + U + Uᵀ) :
    (physicalX V (triangularC U) (triangularK U))ᵀ *
        physicalX V (triangularC U) (triangularK U) = 1 := by
  let C := triangularC U
  let K := triangularK U
  rw [physicalX_gram_expansion]
  have hiso := triangular_isometry_identity hk (Vᵀ * V) U hU hGram
  change Cᵀ * (Vᵀ * V) * C = 1 - Kᵀ * K at hiso
  rw [hiso]
  ext i j
  change (∑ r : Fin k,
      ((K ^ r.1)ᵀ * (1 - Kᵀ * K) * K ^ r.1) i j) = (1 : Mat k k) i j
  have hterms :
      (∑ r : Fin k,
        ((K ^ r.1)ᵀ * (1 - Kᵀ * K) * K ^ r.1) i j) =
      ∑ r : Fin k,
        (((K ^ r.1)ᵀ * K ^ r.1) i j -
          ((K ^ (r.1 + 1))ᵀ * K ^ (r.1 + 1)) i j) := by
    apply Finset.sum_congr rfl
    intro r _hr
    exact congrArg (fun M : Mat k k => M i j) (dilation_gram_summand K r.1)
  rw [hterms]
  have hconvert := Fin.sum_univ_eq_sum_range
    (fun r : ℕ =>
      ((K ^ r)ᵀ * K ^ r) i j - ((K ^ (r + 1))ᵀ * K ^ (r + 1)) i j) k
  rw [hconvert, Finset.sum_range_sub']
  rw [pow_zero, Matrix.transpose_one, one_mul,
    triangularK_pow_card_eq_zero hk U hU, Matrix.transpose_zero, zero_mul]
  exact sub_zero ((1 : Mat k k) i j)




lemma vdot_mulVec_left (A : Mat n k) (x : Vec k) (y : Vec n) :
    vdot (A *ᵥ x) y = vdot x (Aᵀ *ᵥ y) := by
  rw [vdot, vdot, dotProduct_comm]
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  exact dotProduct_comm _ _

lemma vdot_sub_self (x y : Vec n) :
    vdot (x - y) (x - y) =
      vdot x x - vdot x y - vdot y x + vdot y y := by
  simp only [vdot, dotProduct, Pi.sub_apply]
  calc
    ∑ i, (x i - y i) * (x i - y i) =
        ∑ i, (x i * x i - x i * y i - y i * x i + y i * y i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (∑ i, x i * x i) - (∑ i, x i * y i) -
        (∑ i, y i * x i) + ∑ i, y i * y i := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

lemma vdot_add_right (x y z : Vec n) :
    vdot x (y + z) = vdot x y + vdot x z := by
  simp only [vdot, dotProduct, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

lemma vdot_sub_right (x y z : Vec n) :
    vdot x (y - z) = vdot x y - vdot x z := by
  simp only [vdot, dotProduct, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring


def dilationS (V : Mat n k) (C : Mat k k) (w : Vec n) : Vec k :=
  C *ᵥ (Vᵀ *ᵥ w)

def dilationY (V : Mat n k) (C : Mat k k) (w : Vec n) : Vec n :=
  w - V *ᵥ dilationS V C w


theorem one_step_cross (V : Mat n k) (C K : Mat k k) (w : Vec n)
    (hIso : Cᵀ * (Vᵀ * V) * C = 1 - Kᵀ * K)
    (hCK : C + K = 1) :
    Kᵀ *ᵥ dilationS V C w + Cᵀ *ᵥ (Vᵀ *ᵥ dilationY V C w) = 0 := by
  let G : Mat k k := Vᵀ * V
  let a : Vec k := Vᵀ *ᵥ w
  have hcrossMat : Kᵀ * C + Cᵀ - Cᵀ * G * C = 0 := by
    change Cᵀ * G * C = 1 - Kᵀ * K at hIso
    have hK : K = 1 - C := by
      rw [← hCK]
      noncomm_ring
    have hKt : Kᵀ = 1 - Cᵀ := by
      rw [hK, Matrix.transpose_sub, Matrix.transpose_one]
    rw [hIso, hK]
    simp only [Matrix.transpose_sub, Matrix.transpose_one]
    noncomm_ring
  have happ := congrArg (fun M : Mat k k => M *ᵥ a) hcrossMat
  change Kᵀ *ᵥ (C *ᵥ a) + Cᵀ *ᵥ
      (Vᵀ *ᵥ (w - V *ᵥ (C *ᵥ a))) = 0
  rw [Matrix.mulVec_sub, show Vᵀ *ᵥ w = a from rfl,
    Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec (C *ᵥ a) Vᵀ V]
  change (Kᵀ * C) *ᵥ a + Cᵀ *ᵥ
      (a - (Vᵀ * V) *ᵥ (C *ᵥ a)) = 0
  dsimp [G] at happ
  rw [Matrix.mulVec_sub, ← add_sub_assoc]
  simpa only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.zero_mulVec] using happ


theorem one_step_norm (V : Mat n k) (C K : Mat k k) (w : Vec n)
    (hw : vdot w w = 1)
    (hIso : Cᵀ * (Vᵀ * V) * C = 1 - Kᵀ * K)
    (hCK : C + K = 1) :
    vdot (dilationY V C w) (dilationY V C w) +
      vdot (dilationS V C w) (dilationS V C w) = 1 := by
  let G : Mat k k := Vᵀ * V
  let a : Vec k := Vᵀ *ᵥ w
  let s : Vec k := C *ᵥ a
  have hGa : vdot (V *ᵥ s) w = vdot s a := by
    rw [vdot_mulVec_left]
  have hGG : vdot (V *ᵥ s) (V *ᵥ s) = vdot s (G *ᵥ s) := by
    rw [vdot_mulVec_left, Matrix.mulVec_mulVec]
  have hsumMat : Cᵀ * (G + 1) * C = C + Cᵀ := by
    change Cᵀ * G * C = 1 - Kᵀ * K at hIso
    have hK : K = 1 - C := by
      rw [← hCK]
      noncomm_ring
    have hKt : Kᵀ = 1 - Cᵀ := by
      rw [hK, Matrix.transpose_sub, Matrix.transpose_one]
    calc
      Cᵀ * (G + 1) * C = Cᵀ * G * C + Cᵀ * C := by noncomm_ring
      _ = (1 - Kᵀ * K) + Cᵀ * C := by rw [hIso]
      _ = C + Cᵀ := by
        rw [hK]
        simp only [Matrix.transpose_sub, Matrix.transpose_one]
        noncomm_ring
  have hquad : vdot s (G *ᵥ s) + vdot s s =
      2 * vdot a s := by
    have happ := congrArg (fun M : Mat k k => M *ᵥ a) hsumMat
    have hvec : Cᵀ *ᵥ ((G + 1) *ᵥ (C *ᵥ a)) =
        C *ᵥ a + Cᵀ *ᵥ a := by
      calc
        Cᵀ *ᵥ ((G + 1) *ᵥ (C *ᵥ a)) =
            (Cᵀ * (G + 1) * C) *ᵥ a := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        _ = (C + Cᵀ) *ᵥ a := happ
        _ = C *ᵥ a + Cᵀ *ᵥ a := Matrix.add_mulVec _ _ _
    have hdot := congrArg (fun x : Vec k => vdot a x) hvec
    change vdot a (Cᵀ *ᵥ ((G + 1) *ᵥ s)) =
      vdot a (s + Cᵀ *ᵥ a) at hdot
    have hadd : vdot a (s + Cᵀ *ᵥ a) =
        vdot a s + vdot a (Cᵀ *ᵥ a) := by
      exact vdot_add_right _ _ _
    rw [hadd] at hdot
    rw [← vdot_mulVec_left] at hdot
    have hleft : vdot (C *ᵥ a) ((G + 1) *ᵥ s) =
        vdot s (G *ᵥ s) + vdot s s := by
      change vdot s ((G + 1) *ᵥ s) = _
      rw [Matrix.add_mulVec, Matrix.one_mulVec]
      exact vdot_add_right _ _ _
    have hright : vdot a (Cᵀ *ᵥ a) = vdot a s := by
      rw [← vdot_mulVec_left]
      exact dotProduct_comm _ _
    rw [hleft, hright] at hdot
    linarith
  change vdot (w - V *ᵥ s) (w - V *ᵥ s) + vdot s s = 1
  have hcross : vdot w (V *ᵥ s) = vdot s a := by
    rw [vdot, vdot, dotProduct_comm]
    exact hGa
  rw [vdot_sub_self]
  rw [hw, hcross, hGa, hGG]
  have hcomm : vdot a s = vdot s a := dotProduct_comm _ _
  rw [hcomm] at hquad
  linarith





def physicalPBlock (V : Mat n k) (C K : Mat k k) (s : Vec k) (y : Vec n)
    (r : ℕ) : Vec n :=
  if r = 0 then y else (V * C * K ^ (r - 1)) *ᵥ s


def physicalP (V : Mat n k) (C K : Mat k k) (s : Vec k) (y : Vec n) :
    (Fin k × Fin n) → ℝ :=
  fun ri => physicalPBlock V C K s y ri.1 ri.2


lemma dilation_cross_summand (K : Mat k k) (r : ℕ) :
    (K ^ (r + 1))ᵀ * (1 - Kᵀ * K) * K ^ r =
      (K ^ (r + 1))ᵀ * K ^ r -
        (K ^ (r + 2))ᵀ * K ^ (r + 1) := by
  simp only [pow_succ', Matrix.transpose_mul]
  noncomm_ring



lemma physical_cross_block_succ (V : Mat n k) (C K : Mat k k)
    (s : Vec k) (r : ℕ)
    (hIso : Cᵀ * (Vᵀ * V) * C = 1 - Kᵀ * K) :
    (V * C * K ^ (r + 1))ᵀ *ᵥ ((V * C * K ^ r) *ᵥ s) =
      ((K ^ (r + 1))ᵀ * K ^ r) *ᵥ s -
        ((K ^ (r + 2))ᵀ * K ^ (r + 1)) *ᵥ s := by
  have hm : (V * C * K ^ (r + 1))ᵀ * (V * C * K ^ r) =
      (K ^ (r + 1))ᵀ * (1 - Kᵀ * K) * K ^ r := by
    simp only [Matrix.transpose_mul]
    calc
      (K ^ (r + 1))ᵀ * (Cᵀ * Vᵀ) * (V * C * K ^ r) =
          (K ^ (r + 1))ᵀ * (Cᵀ * (Vᵀ * V) * C) * K ^ r := by
        simp only [Matrix.mul_assoc]
      _ = (K ^ (r + 1))ᵀ * (1 - Kᵀ * K) * K ^ r := by rw [hIso]
  rw [Matrix.mulVec_mulVec, hm, dilation_cross_summand,
    Matrix.sub_mulVec]


lemma physical_norm_block (V : Mat n k) (C K : Mat k k)
    (s : Vec k) (r : ℕ)
    (hIso : Cᵀ * (Vᵀ * V) * C = 1 - Kᵀ * K) :
    vdot ((V * C * K ^ r) *ᵥ s) ((V * C * K ^ r) *ᵥ s) =
      vdot (K ^ r *ᵥ s) (K ^ r *ᵥ s) -
        vdot (K ^ (r + 1) *ᵥ s) (K ^ (r + 1) *ᵥ s) := by
  rw [vdot_mulVec_left, Matrix.mulVec_mulVec]
  have hm : (V * C * K ^ r)ᵀ * (V * C * K ^ r) =
      (K ^ r)ᵀ * (1 - Kᵀ * K) * K ^ r := by
    simp only [Matrix.transpose_mul]
    calc
      (K ^ r)ᵀ * (Cᵀ * Vᵀ) * (V * C * K ^ r) =
          (K ^ r)ᵀ * (Cᵀ * (Vᵀ * V) * C) * K ^ r := by
        simp only [Matrix.mul_assoc]
      _ = (K ^ r)ᵀ * (1 - Kᵀ * K) * K ^ r := by rw [hIso]
  rw [hm, dilation_gram_summand, Matrix.sub_mulVec]
  rw [vdot_sub_right]
  have hquad (M : Mat k k) :
      vdot s ((Mᵀ * M) *ᵥ s) = vdot (M *ᵥ s) (M *ᵥ s) := by
    rw [← Matrix.mulVec_mulVec]
    exact (vdot_mulVec_left M s (M *ᵥ s)).symm
  rw [hquad, hquad]



theorem physical_cross_sum (hk : 0 < k) (V : Mat n k) (C K : Mat k k)
    (s : Vec k) (y : Vec n)
    (hIso : Cᵀ * (Vᵀ * V) * C = 1 - Kᵀ * K)
    (hCross : Kᵀ *ᵥ s + Cᵀ *ᵥ (Vᵀ *ᵥ y) = 0)
    (hNil : K ^ k = 0) :
    ∑ r : Fin k,
      (V * C * K ^ r.1)ᵀ *ᵥ physicalPBlock V C K s y r.1 = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  let f : ℕ → Vec (m + 1) := fun r =>
    (V * C * K ^ r)ᵀ *ᵥ physicalPBlock V C K s y r
  let q : ℕ → Vec (m + 1) := fun r =>
    ((K ^ (r + 1))ᵀ * K ^ r) *ᵥ s
  have hf0 : f 0 = -q 0 := by
    ext i
    have hi := congrFun hCross i
    dsimp [f, q, physicalPBlock]
    simp only [pow_zero, pow_one, Matrix.mul_one, Matrix.transpose_mul,
      Matrix.transpose_one, one_mul, Matrix.mulVec_mulVec, Pi.add_apply,
      Pi.neg_apply, Pi.zero_apply] at hi ⊢
    linarith
  have hsucc (r : ℕ) : f (r + 1) = q r - q (r + 1) := by
    simpa [f, q, physicalPBlock, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Nat.add_assoc] using physical_cross_block_succ V C K s r hIso
  have hlast : q m = 0 := by
    have hpow : m + 1 = m + 1 := rfl
    dsimp [q]
    rw [hNil, Matrix.transpose_zero, zero_mul, Matrix.zero_mulVec]
  change ∑ r : Fin (m + 1), f r.1 = 0
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_range_succ']
  have hterms : (∑ r ∈ Finset.range m, f (r + 1)) =
      ∑ r ∈ Finset.range m, (q r - q (r + 1)) := by
    apply Finset.sum_congr rfl
    intro r _hr
    exact hsucc r
  rw [hterms, Finset.sum_range_sub', hf0, hlast]
  dsimp [q]
  simp



theorem physicalX_transpose_mul_p (hk : 0 < k) (V : Mat n k) (C K : Mat k k)
    (s : Vec k) (y : Vec n)
    (hIso : Cᵀ * (Vᵀ * V) * C = 1 - Kᵀ * K)
    (hCross : Kᵀ *ᵥ s + Cᵀ *ᵥ (Vᵀ *ᵥ y) = 0)
    (hNil : K ^ k = 0) :
    (physicalX V C K)ᵀ *ᵥ physicalP V C K s y = 0 := by
  have hsum := physical_cross_sum hk V C K s y hIso hCross hNil
  ext j
  have hj := congrFun hsum j
  change ∑ ri : Fin k × Fin n,
      physicalX V C K ri j * physicalP V C K s y ri = 0
  rw [Fintype.sum_prod_type]
  change ∑ r : Fin k, ∑ i : Fin n,
      (V * C * K ^ r.1) i j * physicalPBlock V C K s y r.1 i = 0
  simpa only [Finset.sum_apply, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
    Pi.zero_apply] using hj


theorem physicalP_dot_self (hk : 0 < k) (V : Mat n k) (C K : Mat k k)
    (s : Vec k) (y : Vec n)
    (hIso : Cᵀ * (Vᵀ * V) * C = 1 - Kᵀ * K)
    (hNorm : vdot y y + vdot s s = 1) :
    physicalP V C K s y ⬝ᵥ physicalP V C K s y =
      1 - vdot (K ^ (k - 1) *ᵥ s) (K ^ (k - 1) *ᵥ s) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  let f : ℕ → ℝ := fun r =>
    vdot (physicalPBlock V C K s y r) (physicalPBlock V C K s y r)
  let q : ℕ → ℝ := fun r => vdot (K ^ r *ᵥ s) (K ^ r *ᵥ s)
  have hf0 : f 0 = vdot y y := by simp [f, physicalPBlock]
  have hsucc (r : ℕ) : f (r + 1) = q r - q (r + 1) := by
    simpa [f, q, physicalPBlock] using physical_norm_block V C K s r hIso
  have hq0 : q 0 = vdot s s := by simp [q]
  change (∑ ri : Fin (m + 1) × Fin n,
      physicalP V C K s y ri * physicalP V C K s y ri) = _
  rw [Fintype.sum_prod_type]
  change (∑ r : Fin (m + 1), f r.1) = _
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_range_succ']
  have hterms : (∑ r ∈ Finset.range m, f (r + 1)) =
      ∑ r ∈ Finset.range m, (q r - q (r + 1)) := by
    apply Finset.sum_congr rfl
    intro r _hr
    exact hsucc r
  rw [hterms, Finset.sum_range_sub', hf0, hq0]
  dsimp [q]
  linarith


theorem physicalP_norm_le_one (hk : 0 < k) (V : Mat n k) (C K : Mat k k)
    (s : Vec k) (y : Vec n)
    (hIso : Cᵀ * (Vᵀ * V) * C = 1 - Kᵀ * K)
    (hNorm : vdot y y + vdot s s = 1) :
    coordNorm (physicalP V C K s y) ≤ 1 := by
  have hdot := physicalP_dot_self hk V C K s y hIso hNorm
  have hterminal : 0 ≤
      vdot (K ^ (k - 1) *ᵥ s) (K ^ (k - 1) *ᵥ s) := by
    rw [← vnorm_sq]
    positivity
  have hsq := coordNorm_sq (physicalP V C K s y)
  rw [hdot] at hsq
  nlinarith [coordNorm_nonneg (physicalP V C K s y)]




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


def physicalFirst (hk : 0 < k) (V : Mat n k) : (Fin k × Fin n) → ℝ :=
  fun ri => if ri.1.1 = 0 then V ri.2 ⟨0, hk⟩ else 0


theorem physicalX_first (hk : 0 < k) (V : Mat n k) (U : Mat k k)
    (hU : StrictUpper U) :
    physicalX V (triangularC U) (triangularK U) *ᵥ firstCoord hk =
      physicalFirst hk V := by
  ext ri
  rcases ri with ⟨r, i⟩
  change ((V * triangularC U * triangularK U ^ r.1) *ᵥ firstCoord hk) i =
    if r.1 = 0 then V i ⟨0, hk⟩ else 0
  by_cases hr : r.1 = 0
  · have hre : r = ⟨0, hk⟩ := Fin.ext hr
    subst r
    simp only [pow_zero, Matrix.mul_one, Fin.isValue, ↓reduceIte]
    rw [← Matrix.mulVec_mulVec, triangularC_first hk U hU]
    simp [Matrix.mulVec, firstCoord, Pi.single_apply]
  · have hrpos : 0 < r.1 := Nat.pos_of_ne_zero hr
    simp only [hr, ↓reduceIte]
    rw [← Matrix.mulVec_mulVec, triangularK_pow_first hk U hU r.1 hrpos,
      Matrix.mulVec_zero]
    rfl



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

end FinitePrecisionLanczos
