import FinitePrecisionLanczos.Core.Dilation


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n k : ℕ}

def lastCoord (hk : 0 < k) : Vec k := Pi.single ⟨k - 1, by omega⟩ 1

def lastOuter {ι : Type*} (hk : 0 < k) (x : ι → ℝ) : Matrix ι (Fin k) ℝ :=
  Matrix.vecMulVec x (lastCoord hk)

lemma lastOuter_smul {ι : Type*} (hk : 0 < k) (b : ℝ) (x : ι → ℝ) :
    lastOuter hk (b • x) = b • lastOuter hk x := by
  ext i j
  simp [lastOuter, Matrix.vecMulVec]
  ring

lemma mul_lastOuter {m : ℕ} (hk : 0 < k) (A : Mat m n) (x : Vec n) :
    A * lastOuter hk x = lastOuter hk (A *ᵥ x) := by
  exact Matrix.mul_vecMulVec A x (lastCoord hk)

lemma lastOuter_mulVec {ι : Type*} (hk : 0 < k) (x : ι → ℝ) (y : Vec k) :
    lastOuter hk x *ᵥ y = y ⟨k - 1, by omega⟩ • x := by
  ext a
  simp [lastOuter, Matrix.vecMulVec, Matrix.mulVec, dotProduct, lastCoord, Pi.single_apply,
    mul_comm]

def powerResidual (K L : Mat k k) : ℕ → Mat k k
  | 0 => 0
  | r + 1 => powerResidual K L r * K + K ^ r * L


def blockDiagonal {p : ℕ} (A : Mat n n) :
    Matrix (Fin p × Fin n) (Fin p × Fin n) ℝ :=
  fun ri sj => if ri.1 = sj.1 then A ri.2 sj.2 else 0

theorem blockDiagonal_mul_stack {p : ℕ} (A : Mat n n) (B : Fin p → Mat n k) :
    blockDiagonal A * stackBlocks B = stackBlocks fun r => A * B r := by
  ext ri j
  rcases ri with ⟨r, i⟩
  simp [blockDiagonal, stackBlocks, Matrix.mul_apply, Fintype.sum_prod_type]

def physicalErrorBlock (V F : Mat n k) (C K : Mat k k) (D : ℕ → Mat k k) (r : ℕ) :
    Mat n k :=
  F * C * K ^ r + V * (D r - D (r + 1))

def physicalError (V F : Mat n k) (C K : Mat k k) (D : ℕ → Mat k k) :
    Matrix (Fin (k + 1) × Fin n) (Fin k) ℝ :=
  stackBlocks fun r : Fin (k + 1) => physicalErrorBlock V F C K D r.1

end FinitePrecisionLanczos
