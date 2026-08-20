import FinitePrecisionLanczos.Core.Dilation

/-!
# Propagating the normalized recurrence through the physical copies

This file is the formal counterpart of `eq:L-commutator` through the
recurrence in `lem:dilation`.  Exact algebra is separated from norm estimates so
that every displayed recurrence in the PDF has a directly checkable Lean
statement.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n k : ℕ}

/-- The last coordinate vector `e_k`. -/
def lastCoord (hk : 0 < k) : Vec k := Pi.single ⟨k - 1, by omega⟩ 1

/-- The rank-one matrix `x e_kᵀ`. -/
def lastOuter {ι : Type*} (hk : 0 < k) (x : ι → ℝ) : Matrix ι (Fin k) ℝ :=
  Matrix.vecMulVec x (lastCoord hk)

lemma lastOuter_add (hk : 0 < k) (x y : Vec n) :
    lastOuter hk (x + y) = lastOuter hk x + lastOuter hk y := by
  ext i j
  simp [lastOuter, Matrix.vecMulVec, add_mul]

lemma lastOuter_sub (hk : 0 < k) (x y : Vec n) :
    lastOuter hk (x - y) = lastOuter hk x - lastOuter hk y := by
  ext i j
  simp [lastOuter, Matrix.vecMulVec, sub_mul]

lemma lastOuter_smul {ι : Type*} (hk : 0 < k) (b : ℝ) (x : ι → ℝ) :
    lastOuter hk (b • x) = b • lastOuter hk x := by
  ext i j
  simp [lastOuter, Matrix.vecMulVec]
  ring

lemma mul_lastOuter {m : ℕ} (hk : 0 < k) (A : Mat m n) (x : Vec n) :
    A * lastOuter hk x = lastOuter hk (A *ᵥ x) := by
  exact Matrix.mul_vecMulVec A x (lastCoord hk)

lemma lastOuter_mul (hk : 0 < k) (x : Vec n) (M : Mat k k) :
    lastOuter hk x * M = Matrix.vecMulVec x (Matrix.vecMul (lastCoord hk) M) := by
  exact Matrix.vecMulVec_mul x (lastCoord hk) M

/-- A strict upper-triangular matrix has zero last row. -/
lemma lastCoord_vecMul_strictUpper (hk : 0 < k) (U : Mat k k)
    (hU : StrictUpper U) : Matrix.vecMul (lastCoord hk) U = 0 := by
  ext j
  simp only [Matrix.vecMul, dotProduct, lastCoord, Pi.single_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Pi.zero_apply]
  apply hU ⟨k - 1, by omega⟩ j
  change ¬k - 1 < j.1
  omega

/-- The last row of `C=(I+U)⁻¹` is `e_kᵀ`. -/
lemma lastCoord_vecMul_triangularC (hk : 0 < k) (U : Mat k k)
    (hU : StrictUpper U) :
    Matrix.vecMul (lastCoord hk) (triangularC U) = lastCoord hk := by
  have hrow : Matrix.vecMul (lastCoord hk) (1 + U) = lastCoord hk := by
    rw [Matrix.vecMul_add, Matrix.vecMul_one,
      lastCoord_vecMul_strictUpper hk U hU, add_zero]
  have hinv := add_one_mul_triangularC hk U hU
  calc
    Matrix.vecMul (lastCoord hk) (triangularC U) =
        Matrix.vecMul (Matrix.vecMul (lastCoord hk) (1 + U))
          (triangularC U) := by rw [hrow]
    _ = Matrix.vecMul (lastCoord hk) ((1 + U) * triangularC U) :=
      Matrix.vecMul_vecMul _ _ _
    _ = lastCoord hk := by rw [hinv]; simp [Matrix.vecMul]

lemma lastCoord_vecMul_triangularK (hk : 0 < k) (U : Mat k k)
    (hU : StrictUpper U) :
    Matrix.vecMul (lastCoord hk) (triangularK U) = 0 := by
  rw [triangularK]
  rw [Matrix.vecMul_sub, Matrix.vecMul_one,
    lastCoord_vecMul_triangularC hk U hU, sub_self]

lemma lastCoord_vecMul_triangularK_pow (hk : 0 < k) (U : Mat k k)
    (hU : StrictUpper U) (r : ℕ) (hr : 0 < r) :
    Matrix.vecMul (lastCoord hk) (triangularK U ^ r) = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [pow_succ']
  rw [← Matrix.vecMul_vecMul, lastCoord_vecMul_triangularK hk U hU]
  simp [Matrix.vecMul]

/-- The exact identity `L=T K-K T-b s e_kᵀ` in
`eq:L-commutator`. -/
theorem transformed_commutator (hk : 0 < k) (T U : Mat k k)
    (a : Vec k) (b : ℝ) (hU : StrictUpper U) :
    let C := triangularC U
    let K := triangularK U
    let s := C *ᵥ a
    C * (T * U - U * T - b • lastOuter hk a) * C =
      T * K - K * T - b • lastOuter hk s := by
  dsimp only
  let C := triangularC U
  let K := triangularK U
  change C * (T * U - U * T - b • lastOuter hk a) * C =
    T * K - K * T - b • lastOuter hk (C *ᵥ a)
  have hC : C = 1 - K := by
    dsimp [K, triangularK]
    module
  have hUC : U * C = K := triangularK_eq_mul hk U hU |>.symm
  have hCU : C * U = K := triangularK_eq_mul' hk U hU |>.symm
  have heC : Matrix.vecMul (lastCoord hk) C = lastCoord hk :=
    lastCoord_vecMul_triangularC hk U hU
  have houterC (x : Vec k) : lastOuter hk x * C = lastOuter hk x := by
    rw [lastOuter_mul, heC]
    rfl
  have hCouter : C * lastOuter hk a = lastOuter hk (C *ᵥ a) :=
    mul_lastOuter hk C a
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  rw [hCouter, houterC]
  have hfirst : C * (T * U) * C = (C * T) * K := by
    calc
      C * (T * U) * C = C * ((T * U) * C) := Matrix.mul_assoc _ _ _
      _ = C * (T * (U * C)) := by rw [Matrix.mul_assoc T U C]
      _ = C * (T * K) := by rw [hUC]
      _ = (C * T) * K := (Matrix.mul_assoc C T K).symm
  have hsecond : C * (U * T) * C = K * (T * C) := by
    calc
      C * (U * T) * C = C * ((U * T) * C) := Matrix.mul_assoc _ _ _
      _ = C * (U * (T * C)) := by rw [Matrix.mul_assoc U T C]
      _ = (C * U) * (T * C) := (Matrix.mul_assoc C U (T * C)).symm
      _ = K * (T * C) := by rw [hCU]
  rw [hfirst, hsecond]
  rw [hC]
  noncomm_ring

/-- Recursive residual in the power commutator. -/
def powerResidual (K L : Mat k k) : ℕ → Mat k k
  | 0 => 0
  | r + 1 => powerResidual K L r * K + K ^ r * L

/-- The iterated exchange identity, with its residual displayed recursively. -/
theorem power_commutator (hk : 0 < k) (T K L : Mat k k)
    (s : Vec k) (b : ℝ)
    (hLast : Matrix.vecMul (lastCoord hk) K = 0)
    (hL : L = T * K - K * T - b • lastOuter hk s) :
    ∀ r : ℕ,
      T * K ^ (r + 1) - K ^ (r + 1) * T =
        b • lastOuter hk (K ^ r *ᵥ s) + powerResidual K L (r + 1) := by
  intro r
  induction r with
  | zero =>
      simp only [powerResidual, pow_zero, pow_one, Matrix.one_mulVec,
        zero_mul, zero_add, one_mul]
      rw [hL]
      module
  | succ r ih =>
      have hTK : T * K - K * T = b • lastOuter hk s + L := by
        rw [hL]
        module
      have hLastPow : Matrix.vecMul (lastCoord hk) (K ^ (r + 1)) = 0 := by
        rw [pow_succ']
        rw [← Matrix.vecMul_vecMul, hLast]
        simp [Matrix.vecMul]
      have hboundary : lastOuter hk (K ^ r *ᵥ s) * K = 0 := by
        rw [lastOuter_mul, hLast]
        ext i j
        simp [Matrix.vecMulVec]
      have hleft : K ^ (r + 1) * lastOuter hk s =
          lastOuter hk (K ^ (r + 1) *ᵥ s) := mul_lastOuter hk _ _
      rw [pow_succ]
      calc
        T * (K ^ (r + 1) * K) - (K ^ (r + 1) * K) * T =
            (T * K ^ (r + 1) - K ^ (r + 1) * T) * K +
              K ^ (r + 1) * (T * K - K * T) := by noncomm_ring
        _ = (b • lastOuter hk (K ^ r *ᵥ s) +
              powerResidual K L (r + 1)) * K +
              K ^ (r + 1) * (b • lastOuter hk s + L) := by
            rw [ih, hTK]
        _ = b • lastOuter hk (K ^ (r + 1) *ᵥ s) +
              powerResidual K L (r + 2) := by
            simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
              Matrix.mul_smul, hboundary, zero_add, powerResidual, hleft]
            module

/-- The base physical-block recurrence, stated independently of norm estimates. -/
theorem VC_recurrence (hk : 0 < k) (A : Mat n n) (V E : Mat n k)
    (T U : Mat k k) (w : Vec n) (a : Vec k) (b : ℝ)
    (hU : StrictUpper U)
    (hRec : A * V = V * T + b • lastOuter hk w + E) :
    let C := triangularC U
    let K := triangularK U
    let s := C *ᵥ a
    let y := w - V *ᵥ s
    let Rcal := T * U - U * T - b • lastOuter hk a
    let L := C * Rcal * C
    A * (V * C) = (V * C) * T + b • lastOuter hk y +
      (E * C - V * L) := by
  dsimp only
  let C := triangularC U
  let K := triangularK U
  let s := C *ᵥ a
  let y := w - V *ᵥ s
  let Rcal := T * U - U * T - b • lastOuter hk a
  let L := C * Rcal * C
  have hL : L = T * K - K * T - b • lastOuter hk s := by
    exact transformed_commutator hk T U a b hU
  have hC : C = 1 - K := by
    dsimp [K, triangularK]
    module
  have hY : lastOuter hk y = lastOuter hk w - lastOuter hk (V *ᵥ s) := by
    exact lastOuter_sub hk w (V *ᵥ s)
  have hVlast : V * lastOuter hk s = lastOuter hk (V *ᵥ s) :=
    mul_lastOuter hk V s
  calc
    A * (V * C) = (A * V) * C := by simp [Matrix.mul_assoc]
    _ = (V * T + b • lastOuter hk w + E) * C := by rw [hRec]
    _ = V * T * C + b • lastOuter hk w + E * C := by
      rw [Matrix.add_mul, Matrix.add_mul,
        Matrix.smul_mul, lastOuter_mul,
        lastCoord_vecMul_triangularC hk U hU]
      rfl
    _ = (V * C) * T + b • lastOuter hk y + (E * C - V * L) := by
      rw [hY, hL, hC]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        hVlast, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
      module

/-! ## Stacking the propagated blocks -/

/-- `I_k ⊗ A` on the literal product coordinate type. -/
def blockDiagonal (A : Mat n n) :
    Matrix (Fin k × Fin n) (Fin k × Fin n) ℝ :=
  fun ri sj => if ri.1 = sj.1 then A ri.2 sj.2 else 0

/-- A block diagonal operator acts separately on every stacked block. -/
theorem blockDiagonal_mul_stack (A : Mat n n) (B : Fin k → Mat n k) :
    blockDiagonal A * stackBlocks B = stackBlocks fun r => A * B r := by
  ext ri j
  rcases ri with ⟨r, i⟩
  simp [blockDiagonal, stackBlocks, Matrix.mul_apply, Fintype.sum_prod_type]

/-- Block errors in the recurrence of `lem:dilation`. -/
def physicalErrorBlock (V E0 : Mat n k) (C K L : Mat k k) (r : ℕ) :
    Mat n k :=
  if r = 0 then E0 else E0 * K ^ r + V * C * powerResidual K L r

/-- The residual recursion printed after `eq:block-recurrence`.  Keeping this
as a separate exact identity makes the induction in the PDF directly
auditable. -/
theorem physicalErrorBlock_succ (V E0 : Mat n k) (C K L : Mat k k) (r : ℕ) :
    physicalErrorBlock V E0 C K L (r + 1) =
      physicalErrorBlock V E0 C K L r * K + (V * C * K ^ r) * L := by
  by_cases hr : r = 0
  · subst r
    simp [physicalErrorBlock, powerResidual]
  · rw [physicalErrorBlock, if_neg (by omega), physicalErrorBlock, if_neg hr,
      powerResidual, pow_succ]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    module

def physicalError (V E0 : Mat n k) (C K L : Mat k k) :
    Matrix (Fin k × Fin n) (Fin k) ℝ :=
  stackBlocks fun r => physicalErrorBlock V E0 C K L r.1

/-- The positive-index block identity used in
`lem:dilation`. -/
theorem propagated_block_succ (hk : 0 < k) (A : Mat n n) (V E0 : Mat n k)
    (T U : Mat k k) (s : Vec k) (y : Vec n) (b : ℝ) (r : ℕ)
    (hU : StrictUpper U)
    (hVC : A * (V * triangularC U) =
      (V * triangularC U) * T + b • lastOuter hk y + E0)
    (hL : triangularC U *
        (T * U - U * T - b • lastOuter hk ((1 + U) *ᵥ s)) * triangularC U =
      T * triangularK U - triangularK U * T - b • lastOuter hk s) :
    A * (V * triangularC U * triangularK U ^ (r + 1)) =
      (V * triangularC U * triangularK U ^ (r + 1)) * T +
        b • lastOuter hk ((V * triangularC U * triangularK U ^ r) *ᵥ s) +
        (E0 * triangularK U ^ (r + 1) +
          V * triangularC U *
            powerResidual (triangularK U)
              (triangularC U *
                (T * U - U * T - b • lastOuter hk ((1 + U) *ᵥ s)) *
                triangularC U) (r + 1)) := by
  let C := triangularC U
  let K := triangularK U
  let L := C * (T * U - U * T - b • lastOuter hk ((1 + U) *ᵥ s)) * C
  change A * (V * C * K ^ (r + 1)) =
    (V * C * K ^ (r + 1)) * T +
      b • lastOuter hk ((V * C * K ^ r) *ᵥ s) +
      (E0 * K ^ (r + 1) + V * C * powerResidual K L (r + 1))
  have hLast := lastCoord_vecMul_triangularK hk U hU
  have hLastPow := lastCoord_vecMul_triangularK_pow hk U hU (r + 1) (by omega)
  have hBoundaryZero : lastOuter hk y * K ^ (r + 1) = 0 := by
    rw [lastOuter_mul, hLastPow]
    ext i j
    simp [Matrix.vecMulVec]
  have hPower := power_commutator hk T K L s b hLast hL r
  calc
    A * (V * C * K ^ (r + 1)) = (A * (V * C)) * K ^ (r + 1) := by
      simp only [Matrix.mul_assoc]
    _ = ((V * C) * T + b • lastOuter hk y + E0) * K ^ (r + 1) := by
      rw [hVC]
    _ = V * C * (T * K ^ (r + 1)) + E0 * K ^ (r + 1) := by
      rw [Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, hBoundaryZero,
        smul_zero, add_zero]
      simp only [Matrix.mul_assoc]
    _ = V * C *
          (K ^ (r + 1) * T + b • lastOuter hk (K ^ r *ᵥ s) +
            powerResidual K L (r + 1)) + E0 * K ^ (r + 1) := by
      have hPower' : T * K ^ (r + 1) =
          K ^ (r + 1) * T + b • lastOuter hk (K ^ r *ᵥ s) +
            powerResidual K L (r + 1) := by
        calc
          T * K ^ (r + 1) =
              (T * K ^ (r + 1) - K ^ (r + 1) * T) +
                K ^ (r + 1) * T := by module
          _ = (b • lastOuter hk (K ^ r *ᵥ s) +
                powerResidual K L (r + 1)) + K ^ (r + 1) * T := by rw [hPower]
          _ = K ^ (r + 1) * T + b • lastOuter hk (K ^ r *ᵥ s) +
                powerResidual K L (r + 1) := by module
      rw [hPower']
    _ = (V * C * K ^ (r + 1)) * T +
          b • lastOuter hk ((V * C * K ^ r) *ᵥ s) +
          (E0 * K ^ (r + 1) + V * C * powerResidual K L (r + 1)) := by
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc,
        mul_lastOuter, Matrix.mulVec_mulVec]
      module

/-- Exact stacked recurrence in `lem:dilation`. -/
theorem physical_dilation_recurrence (hk : 0 < k) (A : Mat n n)
    (V E : Mat n k) (T U : Mat k k) (w : Vec n) (a : Vec k) (b : ℝ)
    (hU : StrictUpper U)
    (hRec : A * V = V * T + b • lastOuter hk w + E) :
    let C := triangularC U
    let K := triangularK U
    let s := C *ᵥ a
    let y := w - V *ᵥ s
    let Rcal := T * U - U * T - b • lastOuter hk a
    let L := C * Rcal * C
    let E0 := E * C - V * L
    blockDiagonal A * physicalX V C K =
      physicalX V C K * T + b • lastOuter hk (physicalP V C K s y) +
        physicalError V E0 C K L := by
  dsimp only
  let C := triangularC U
  let K := triangularK U
  let s := C *ᵥ a
  let y := w - V *ᵥ s
  let Rcal := T * U - U * T - b • lastOuter hk a
  let L := C * Rcal * C
  let E0 := E * C - V * L
  have hVC : A * (V * C) = (V * C) * T + b • lastOuter hk y + E0 :=
    VC_recurrence hk A V E T U w a b hU hRec
  have ha : (1 + U) *ᵥ s = a := by
    dsimp [s, C]
    rw [Matrix.mulVec_mulVec, add_one_mul_triangularC hk U hU,
      Matrix.one_mulVec]
  have hL : L = T * K - K * T - b • lastOuter hk s := by
    exact transformed_commutator hk T U a b hU
  rw [physicalX, blockDiagonal_mul_stack]
  ext ri j
  rcases ri with ⟨r, i⟩
  change (A * (V * C * K ^ r.1)) i j =
    ((V * C * K ^ r.1) * T) i j +
      (b • lastOuter hk (physicalP V C K s y)) (r, i) j +
      physicalErrorBlock V E0 C K L r.1 i j
  by_cases hr : r.1 = 0
  · have hre : r = ⟨0, hk⟩ := Fin.ext hr
    subst r
    simp only [pow_zero, Matrix.mul_one, physicalP, physicalPBlock,
      physicalErrorBlock, ↓reduceIte, lastOuter, Matrix.vecMulVec,
      Pi.smul_apply, smul_eq_mul]
    have hij := congrArg (fun M : Mat n k => M i j) hVC
    simpa [Matrix.add_apply, Matrix.smul_apply, lastOuter,
      Matrix.vecMulVec] using hij
  · have hrpos : 0 < r.1 := Nat.pos_of_ne_zero hr
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
    have hblock := propagated_block_succ hk A V E0 T U s y b t hU hVC (by
      rw [ha]
      exact hL)
    have hij := congrArg (fun M : Mat n k => M i j) hblock
    have hre : r = ⟨t + 1, by omega⟩ := Fin.ext ht
    rw [hre]
    simpa [physicalP, physicalPBlock, physicalErrorBlock, lastOuter,
      Matrix.vecMulVec, Matrix.add_apply, Matrix.smul_apply,
      ha, L, Rcal, C, K] using hij

end FinitePrecisionLanczos
