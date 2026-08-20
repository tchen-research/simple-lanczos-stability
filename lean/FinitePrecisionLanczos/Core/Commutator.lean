/-
# The commutator identity and the Paige sandwich (paper §5, §6)

Both statements here are *generic*: they mention no Lanczos object, only a
symmetric matrix, a family of columns, and a residual.  That is deliberate.
The paper's §5 proves the commutator identity from three premises -- the
governing relation and symmetry of `H` and of `T` -- and nothing else, so the
Lean statement takes exactly those three as hypotheses and is reusable at every
prefix length.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

namespace FinitePrecisionLanczos.Core

open Matrix

variable {n k : ℕ}

/-! ### The commutator identity (paper Lemma 5.1, equation (26)) -/

/-- **The commutator identity**, paper (26).

If `H * V = V * T + B + F` with `H` and `T` symmetric, then the Gram defect
`Ω = Vᵀ V - 1` almost commutes with `T`: the discrepancy is the boundary term
`C = Vᵀ B`, antisymmetrized, plus the roundoff term `G = Vᵀ F - Fᵀ V`.

Nothing is assumed to be small.  This is the point of the identity: `Ω` may
have any size at all and the constraint still holds. -/
theorem commutator_of_governing
    (H : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin n) (Fin k) ℝ)
    (T : Matrix (Fin k) (Fin k) ℝ) (B F : Matrix (Fin n) (Fin k) ℝ)
    (hH : Hᵀ = H) (hT : Tᵀ = T)
    (hgov : H * V = V * T + B + F) :
    T * (Vᵀ * V - 1) - (Vᵀ * V - 1) * T
      = (Vᵀ * B) - (Vᵀ * B)ᵀ + (Vᵀ * F - Fᵀ * V) := by
  -- project the governing relation
  have key : Vᵀ * (H * V) = (Vᵀ * V) * T + Vᵀ * B + Vᵀ * F := by
    rw [hgov, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc]
  -- the projected matrix is symmetric, because `H` is
  have hsymm : (Vᵀ * (H * V))ᵀ = Vᵀ * (H * V) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hH, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  -- transpose the projection and use symmetry of `T` and of `Vᵀ V`
  have key' : Vᵀ * (H * V) = T * (Vᵀ * V) + (Vᵀ * B)ᵀ + Fᵀ * V := by
    rw [← hsymm, key]
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, hT]
  -- equate the two expressions and cancel
  have := key.symm.trans key'
  have hmul : (Vᵀ * V) * T - T * (Vᵀ * V)
      = (Vᵀ * B)ᵀ + Fᵀ * V - (Vᵀ * B) - Vᵀ * F := by
    rw [sub_eq_iff_eq_add]
    rw [show (Vᵀ * B)ᵀ + Fᵀ * V - Vᵀ * B - Vᵀ * F + T * (Vᵀ * V)
        = (T * (Vᵀ * V) + (Vᵀ * B)ᵀ + Fᵀ * V) - Vᵀ * B - Vᵀ * F by abel]
    rw [← this]
    abel
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
  rw [show T * (Vᵀ * V) - T - ((Vᵀ * V) * T - T)
      = -((Vᵀ * V) * T - T * (Vᵀ * V)) by abel]
  rw [hmul]
  abel

/-! ### The Paige sandwich (paper Theorem 6.2) -/

/-- **The eigenvector sandwich annihilates a commutator**: for symmetric `T`
and any `R`, an eigenvector of `T` kills `T * R - R * T`.

This is the three-line step that turns the upper-triangular identity into
Paige's theorem: the left-hand side of (29) vanishes, so the boundary term is
expressed exactly by the local products and the remainder. -/
theorem sandwich_eq_zero
    (T R : Matrix (Fin k) (Fin k) ℝ) (hT : Tᵀ = T)
    (y : Fin k → ℝ) (θ : ℝ) (hy : T *ᵥ y = θ • y) :
    y ⬝ᵥ ((T * R - R * T) *ᵥ y) = 0 := by
  have h1 : y ⬝ᵥ ((T * R) *ᵥ y) = θ * (y ⬝ᵥ (R *ᵥ y)) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, hy]
    rw [smul_dotProduct, smul_eq_mul]
  have h2 : y ⬝ᵥ ((R * T) *ᵥ y) = θ * (y ⬝ᵥ (R *ᵥ y)) := by
    rw [← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  rw [Matrix.sub_mulVec, dotProduct_sub, h1, h2, sub_self]

/-- **Paige's theorem, algebraic core** (paper Theorem 6.2).

Given the upper-triangular identity (29) in the shape `T * R - R * T = C + N + E`
-- boundary, local products, remainder -- the eigenvector sandwich turns it into
an exact expression for the boundary quadratic form.  Sandwiching `C` is what
produces the physical scalar `β_k (z_iᵀ v_{k+1}) y_{i,k}` of (41).

The upper-triangular identity itself is a *hypothesis* here: deriving it needs
the tridiagonal structure of `T`, which is not yet formalized. -/
theorem paige_sandwich
    (T R C N E : Matrix (Fin k) (Fin k) ℝ) (hT : Tᵀ = T)
    (y : Fin k → ℝ) (θ : ℝ) (hy : T *ᵥ y = θ • y)
    (hupper : T * R - R * T = C + N + E) :
    y ⬝ᵥ (C *ᵥ y) = -(y ⬝ᵥ (N *ᵥ y)) - y ⬝ᵥ (E *ᵥ y) := by
  have h0 := sandwich_eq_zero T R hT y θ hy
  rw [hupper] at h0
  rw [Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add] at h0
  linarith [h0]

/-- The quadratic form of a diagonal matrix splits into a weighted sum of
squares: the step that turns the block-diagonal term `N` of (29) into the sum
`∑_j y_{i,j}^2 (p_j - p_{j-1})` of (41). -/
theorem dotProduct_diagonal_mulVec (d y : Fin k → ℝ) :
    y ⬝ᵥ ((Matrix.diagonal d) *ᵥ y) = ∑ j, d j * (y j) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, Matrix.diagonal, Matrix.of_apply, dotProduct,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### The exact coefficient identity (paper §8, equation (57)) -/

/-- **The division-free coefficient identity**, paper (57).

`S` is a leading principal submatrix, `yhat` the corresponding block of an
eigenvector of the larger matrix, and `hrow` says what rows `1, …, s` of the
larger eigenvalue equation read.  Projecting onto an eigenvector `yr` of `S`
gives the identity in a form with no denominator, so it is valid even when
`θ` is an eigenvalue of `S` -- the case §7 had to exclude by hand.

Reading it left to right bounds the gap `θ - θr`; reading it right to left
bounds the prefix residual `β * ys`.  That is the whole mechanism of the
descent step. -/
theorem coeff_product {s : ℕ}
    (S : Matrix (Fin s) (Fin s) ℝ) (hS : Sᵀ = S)
    (yhat es yr : Fin s → ℝ) (θ θr βys : ℝ)
    (hrow : S *ᵥ yhat = θ • yhat - βys • es)
    (hyr : S *ᵥ yr = θr • yr) :
    (θ - θr) * (yr ⬝ᵥ yhat) = βys * (yr ⬝ᵥ es) := by
  have left : yr ⬝ᵥ (S *ᵥ yhat) = θr * (yr ⬝ᵥ yhat) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS, hyr,
      smul_dotProduct, smul_eq_mul]
  have right : yr ⬝ᵥ (S *ᵥ yhat) = θ * (yr ⬝ᵥ yhat) - βys * (yr ⬝ᵥ es) := by
    rw [hrow, dotProduct_sub, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
  have := left.symm.trans right
  linarith [this]

end FinitePrecisionLanczos.Core
