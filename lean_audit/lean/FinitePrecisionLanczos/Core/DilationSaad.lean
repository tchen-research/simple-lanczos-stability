import FinitePrecisionLanczos.Core.DilationBounds
import FinitePrecisionLanczos.Core.Underline


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n k : ℕ}

lemma stackBlocks_mul {p m : ℕ} {κ : Type*} (B : Fin p → Mat n m) (X : Matrix (Fin m) κ ℝ) :
    stackBlocks B * X = fun ri j => (B ri.1 * X) ri.2 j := by
  ext ri j
  simp [stackBlocks, Matrix.mul_apply]

theorem power_exchange_of_commutator (Tu : Mat (k + 1) k) (K' : Mat (k + 1) (k + 1))
    (K L : Mat k k) (hK'up : Upper K') (hKl : leadBlock K' = K)
    (hex : Tu * K - K' * Tu = padRow L) (r : ℕ) :
    Tu * K ^ r - K' ^ r * Tu = padRow (powerResidual K L r) := by
  have hTK : Tu * K = K' * Tu + padRow L := by rw [← hex]; abel
  induction r with
  | zero => simp [powerResidual]
  | succ r ih =>
      have ih' : Tu * K ^ r = K' ^ r * Tu + padRow (powerResidual K L r) := by
        rw [← ih]; abel
      calc
        Tu * K ^ (r + 1) - K' ^ (r + 1) * Tu
            = (Tu * K ^ r) * K - K' ^ (r + 1) * Tu := by rw [pow_succ, Matrix.mul_assoc]
        _ = K' ^ r * (Tu * K) + padRow (powerResidual K L r) * K - K' ^ (r + 1) * Tu := by
          rw [ih', Matrix.add_mul, Matrix.mul_assoc]
        _ = padRow (powerResidual K L (r + 1)) := by
          rw [hTK, Matrix.mul_add, upper_mul_padRow _ (hK'up.pow r), leadBlock_pow _ hK'up,
            hKl, padRow_mul, powerResidual, padRow_add, pow_succ, Matrix.mul_assoc]
          abel

section Saad

variable (hk : 0 < k) (A : Mat n n) (Vs : Mat n (k + 1)) (V F : Mat n k)
  (T : Mat k k) (β : ℝ) (Us : Mat (k + 1) (k + 1)) (U M : Mat k k)

include hk

theorem saad_commutator_block (c : Fin k → ℝ) (hU : StrictUpper U)
    (hlead : leadBlock Us = U) (hcol : ∀ i : Fin k, Us i.castSucc (Fin.last k) = c i)
    (hlast : ∀ j, Us (Fin.last k) j = 0) :
    underlineT T β * U - Us * underlineT T β =
      padRow (T * U - U * T - β • lastOuter hk c) := by
  have hUs : ∀ i j : Fin k, Us i.castSucc j.castSucc = U i j := fun i j => by
    rw [← hlead]; rfl
  ext i j
  induction i using Fin.lastCases with
  | last =>
      simp only [Matrix.sub_apply, Matrix.mul_apply, underlineT_last, hlast, zero_mul,
        Finset.sum_const_zero, sub_zero, padRow_last]
      apply Finset.sum_eq_zero
      intro m _
      split_ifs with hm
      · rw [hU m j (by omega), mul_zero]
      · rw [zero_mul]
  | cast i =>
      simp only [Matrix.sub_apply, padRow_castSucc, Matrix.smul_apply, lastOuter_apply,
        Matrix.mul_apply]
      rw [Fin.sum_univ_castSucc]
      simp only [underlineT_castSucc, underlineT_last, hUs, hcol, smul_eq_mul]
      split_ifs <;> ring

theorem saad_exchange (hUs : StrictUpper Us) (hlead : leadBlock Us = U)
    (hM : underlineT T β * U - Us * underlineT T β = padRow M) :
    underlineT T β * triangularK U - triangularK Us * underlineT T β =
      padRow (triangularC U * M * triangularC U) := by
  have hU : StrictUpper U := hlead ▸ hUs.leadBlock
  set Tu := underlineT T β
  set C' := triangularC Us
  set K' := triangularK Us
  set C := triangularC U
  set K := triangularK U
  have hK : K = U * C := triangularK_eq_mul hk U hU
  have hK' : K' = C' * Us := triangularK_eq_mul' (Nat.succ_pos k) Us hUs
  have hC : C = 1 - K := by rw [show K = 1 - C from rfl]; abel
  have hC' : C' = 1 - K' := by rw [show K' = 1 - C' from rfl]; abel
  have hCl : leadBlock C' = C := by
    rw [leadBlock_triangularC hk Us hUs, hlead]
  have key : C' * (Tu * U - Us * Tu) * C = padRow (C * M * C) := by
    rw [hM, upper_mul_padRow C' (triangularC_upper Us hUs), padRow_mul, hCl]
  calc
    Tu * K - K' * Tu = (1 - K') * Tu * K - K' * Tu * (1 - K) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_assoc]
      abel
    _ = C' * Tu * K - K' * Tu * C := by rw [← hC', ← hC]
    _ = C' * (Tu * U - Us * Tu) * C := by
      rw [hK, hK', Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_assoc]
    _ = padRow (C * M * C) := key

theorem saad_leadCols_block (hUs : StrictUpper Us) (hlead : leadBlock Us = U)
    (hV : leadCols Vs = V) (r : ℕ) :
    leadCols (Vs * triangularC Us * triangularK Us ^ r) =
      V * triangularC U * triangularK U ^ r := by
  have hC'up := triangularC_upper Us hUs
  have hK'up := triangularK_upper (Nat.succ_pos k) Us hUs
  rw [Matrix.mul_assoc, leadCols_mul _ _ (hC'up.mul (hK'up.pow r)),
    leadBlock_mul _ _ (hK'up.pow r), leadBlock_pow _ hK'up,
    leadBlock_triangularC hk Us hUs, leadBlock_triangularK hk Us hUs, hlead, hV,
    Matrix.mul_assoc]

end Saad

section Recurrence

variable (A : Mat n n) (Vs : Mat n (k + 1)) (V F : Mat n k) (Tu : Mat (k + 1) k)
  (C' K' : Mat (k + 1) (k + 1)) (C K : Mat k k) (D : ℕ → Mat k k)

theorem saad_block_recurrence (hV : leadCols Vs = V) (hrec : A * V = Vs * Tu + F)
    (hC' : C' = 1 - K') (hC : C = 1 - K)
    (hpow : ∀ r : ℕ, Tu * K ^ r - K' ^ r * Tu = padRow (D r)) (r : ℕ) :
    A * (V * C * K ^ r) = (Vs * C' * K' ^ r) * Tu + physicalErrorBlock V F C K D r := by
  rw [physicalErrorBlock]
  have hVpad (X : Mat k k) : Vs * padRow X = V * X := by rw [mul_padRow, hV]
  have hpow0 : Tu * K ^ r = K' ^ r * Tu + padRow (D r) := by rw [← hpow r]; abel
  have hpow1 : Tu * K ^ (r + 1) = K' ^ (r + 1) * Tu + padRow (D (r + 1)) := by
    rw [← hpow (r + 1)]; abel
  have hparen : Tu * (C * K ^ r) = C' * K' ^ r * Tu + padRow (D r - D (r + 1)) := by
    have hCK : C * K ^ r = K ^ r - K ^ (r + 1) := by
      rw [hC, Matrix.sub_mul, Matrix.one_mul, pow_succ']
    have hCK' : C' * K' ^ r = K' ^ r - K' ^ (r + 1) := by
      rw [hC', Matrix.sub_mul, Matrix.one_mul, pow_succ']
    rw [hCK, hCK', Matrix.mul_sub, hpow0, hpow1, padRow_sub, Matrix.sub_mul]
    abel
  calc
    A * (V * C * K ^ r) = (A * V) * (C * K ^ r) := by simp only [Matrix.mul_assoc]
    _ = Vs * (Tu * (C * K ^ r)) + F * C * K ^ r := by
      rw [hrec]; simp only [Matrix.add_mul, Matrix.mul_assoc]
    _ = Vs * C' * K' ^ r * Tu + (F * C * K ^ r + V * (D r - D (r + 1))) := by
      rw [hparen, Matrix.mul_add, hVpad]
      simp only [Matrix.mul_assoc]
      abel

theorem saad_dilation_recurrence
    (hlc : ∀ r : ℕ, leadCols (Vs * C' * K' ^ r) = V * C * K ^ r)
    (hV : leadCols Vs = V) (hrec : A * V = Vs * Tu + F)
    (hC' : C' = 1 - K') (hC : C = 1 - K)
    (hpow : ∀ r : ℕ, Tu * K ^ r - K' ^ r * Tu = padRow (D r)) :
    blockDiagonal A * leadCols (dilationStack (k + 1) Vs C' K') =
      dilationStack (k + 1) Vs C' K' * Tu + physicalError V F C K D := by
  have hstack : leadCols (dilationStack (k + 1) Vs C' K') =
      stackBlocks fun r : Fin (k + 1) => V * C * K ^ r.1 := by
    ext ri j
    have h := congrFun (congrFun (hlc ri.1.1) ri.2) j
    simpa [dilationStack, stackBlocks, leadCols] using h
  rw [hstack, blockDiagonal_mul_stack, dilationStack, stackBlocks_mul]
  ext ri j
  have h := congrFun (congrFun
    (saad_block_recurrence A Vs V F Tu C' K' C K D hV hrec hC' hC hpow ri.1.1) ri.2) j
  simpa [stackBlocks, physicalError, Matrix.add_apply] using h

end Recurrence

end FinitePrecisionLanczos
