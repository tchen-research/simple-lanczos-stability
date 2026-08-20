import FinitePrecisionLanczos.Lanczos.Greenbaum.Interface
import Mathlib.Algebra.Ring.GeomSum









namespace FinitePrecisionLanczos

open Matrix

variable {k : ℕ}


def StrictUpper (U : Mat k k) : Prop :=
  ∀ i j, ¬i.1 < j.1 → U i j = 0


def Upper (U : Mat k k) : Prop :=
  ∀ i j, j.1 < i.1 → U i j = 0


theorem StrictUpper.pow_entry_zero (U : Mat k k) (hU : StrictUpper U) :
    ∀ r : ℕ, ∀ i j : Fin k, j.1 < i.1 + r → (U ^ r) i j = 0 := by
  intro r
  induction r with
  | zero =>
      intro i j hij
      simp only [pow_zero, Matrix.one_apply]
      exact if_neg (by intro h; subst j; omega)
  | succ r ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro m _hm
      by_cases him : m.1 < i.1 + r
      · rw [ih i m him, zero_mul]
      · have hmj : ¬m.1 < j.1 := by omega
        rw [hU m j hmj, mul_zero]


theorem StrictUpper.pow_card_eq_zero (U : Mat k k) (hU : StrictUpper U) :
    U ^ k = 0 := by
  ext i j
  exact StrictUpper.pow_entry_zero U hU k i j (by omega)

lemma StrictUpper.upper (U : Mat k k) (hU : StrictUpper U) : Upper U := by
  intro i j hji
  exact hU i j (by omega)

lemma Upper.one : Upper (1 : Mat k k) := by
  intro i j hji
  have hij : i ≠ j := by
    intro h
    subst j
    omega
  simp [Matrix.one_apply, hij]

lemma Upper.zero : Upper (0 : Mat k k) := by
  intro i j hji
  rfl

lemma Upper.add {A B : Mat k k} (hA : Upper A) (hB : Upper B) : Upper (A + B) := by
  intro i j hji
  simp [hA i j hji, hB i j hji]

lemma Upper.sum {ι : Type*} {s : Finset ι} {A : ι → Mat k k}
    (hA : ∀ i ∈ s, Upper (A i)) : Upper (s.sum A) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Upper.zero : Upper (0 : Mat k k))
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Upper.add (hA a (Finset.mem_insert_self a s))
        (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))

lemma StrictUpper.pow_upper (U : Mat k k) (hU : StrictUpper U) (r : ℕ) :
    Upper (U ^ r) := by
  intro i j hji
  exact StrictUpper.pow_entry_zero U hU r i j (by omega)

lemma StrictUpper.neg (U : Mat k k) (hU : StrictUpper U) : StrictUpper (-U) := by
  intro i j hij
  simp [hU i j hij]

lemma StrictUpper.neg_pow_upper (U : Mat k k) (hU : StrictUpper U) (r : ℕ) :
    Upper ((-U) ^ r) := by
  exact StrictUpper.pow_upper (-U) (StrictUpper.neg U hU) r


def triangularC (U : Mat k k) : Mat k k :=
  (Finset.range k).sum fun r => (-U) ^ r


def triangularK (U : Mat k k) : Mat k k := 1 - triangularC U

lemma triangularC_upper (U : Mat k k) (hU : StrictUpper U) :
    Upper (triangularC U) := by
  apply Upper.sum
  intro r hr
  exact StrictUpper.neg_pow_upper U hU r

lemma neg_pow_card_eq_zero (U : Mat k k) (hU : StrictUpper U) :
    (-U) ^ k = 0 := by
  exact StrictUpper.pow_card_eq_zero (-U) (StrictUpper.neg U hU)


theorem add_one_mul_triangularC (hk : 0 < k) (U : Mat k k) (hU : StrictUpper U) :
    (1 + U) * triangularC U = 1 := by
  have hgeom := mul_neg_geom_sum (-U) k
  rw [neg_pow_card_eq_zero U hU] at hgeom
  simpa [triangularC] using hgeom


theorem triangularC_mul_add_one (hk : 0 < k) (U : Mat k k) (hU : StrictUpper U) :
    triangularC U * (1 + U) = 1 := by
  have hgeom := geom_sum_mul_neg (-U) k
  rw [neg_pow_card_eq_zero U hU] at hgeom
  simpa [triangularC] using hgeom


theorem triangularK_eq_mul (hk : 0 < k) (U : Mat k k) (hU : StrictUpper U) :
    triangularK U = U * triangularC U := by
  have hinv := add_one_mul_triangularC hk U hU
  dsimp [triangularK]
  calc
    1 - triangularC U = (1 + U) * triangularC U - triangularC U := by rw [hinv]
    _ = U * triangularC U := by noncomm_ring


theorem triangularK_eq_mul' (hk : 0 < k) (U : Mat k k) (hU : StrictUpper U) :
    triangularK U = triangularC U * U := by
  have hinv := triangularC_mul_add_one hk U hU
  dsimp [triangularK]
  calc
    1 - triangularC U = triangularC U * (1 + U) - triangularC U := by rw [hinv]
    _ = triangularC U * U := by noncomm_ring

lemma StrictUpper.mul_upper {U C : Mat k k} (hU : StrictUpper U) (hC : Upper C) :
    StrictUpper (U * C) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro m _hm
  by_cases him : i.1 < m.1
  · have hmj : j.1 < m.1 := by omega
    rw [hC m j hmj, mul_zero]
  · rw [hU i m him, zero_mul]

lemma triangularK_strictUpper (hk : 0 < k) (U : Mat k k) (hU : StrictUpper U) :
    StrictUpper (triangularK U) := by
  rw [triangularK_eq_mul hk U hU]
  exact hU.mul_upper (triangularC_upper U hU)

lemma triangularK_pow_card_eq_zero (hk : 0 < k) (U : Mat k k)
    (hU : StrictUpper U) : triangularK U ^ k = 0 :=
  StrictUpper.pow_card_eq_zero _ (triangularK_strictUpper hk U hU)


theorem triangular_isometry_identity (hk : 0 < k)
    (G U : Mat k k) (hU : StrictUpper U)
    (hG : G = 1 + U + Uᵀ) :
    (triangularC U)ᵀ * G * triangularC U =
      1 - (triangularK U)ᵀ * triangularK U := by
  let C := triangularC U
  let K := triangularK U
  have hK : K = 1 - C := rfl
  have hUC : U * C = K := (triangularK_eq_mul hk U hU).symm
  have hUt : Cᵀ * Uᵀ = Kᵀ := by
    have := congrArg Matrix.transpose hUC
    simpa [Matrix.transpose_mul] using this
  have hKt : Kᵀ = 1 - Cᵀ := by
    have := congrArg Matrix.transpose hK
    simpa using this
  rw [hG]
  change Cᵀ * (1 + U + Uᵀ) * C = 1 - Kᵀ * K
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
    Matrix.add_mul, Matrix.mul_assoc Cᵀ U C, hUC, hUt]
  rw [hK, Matrix.transpose_sub, Matrix.transpose_one]
  noncomm_ring

end FinitePrecisionLanczos
