import FinitePrecisionLanczos.Lanczos.Greenbaum.Backward
import FinitePrecisionLanczos.Core.BlockSpectral


namespace FinitePrecisionLanczos

open _root_.Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

lemma greenbaumVhat_underlineTmat_mulVec (y : Vec k) :
    (L.greenbaumVhat * L.underlineTmat) *ᵥ y =
      L.greenbaumX *ᵥ (L.Tmat *ᵥ y) + (L.β k * y (lastIndex L.hk_pos)) • L.greenbaumVNext := by
  rw [underlineTmat, mul_underlineT L.hk_pos, Matrix.add_mulVec, Matrix.smul_mulVec,
    lastOuter_mulVec, ← Matrix.mulVec_mulVec, smul_smul]
  rfl

theorem greenbaum_ritz_residual (y : Vec k) (theta : ℝ)
    (heig : L.Tmat *ᵥ y = theta • y) :
    L.greenbaumTildeA *ᵥ (L.greenbaumX *ᵥ y) - theta • (L.greenbaumX *ᵥ y) =
      (L.β k * y (lastIndex L.hk_pos)) • L.greenbaumVNext := by
  rw [Matrix.mulVec_mulVec, L.greenbaum_backward_model.recurrence,
    greenbaumVhat_underlineTmat_mulVec, heig, Matrix.mulVec_smul]
  abel

lemma coordNorm_greenbaumX_mulVec (y : Vec k) (hy : vdot y y = 1) :
    coordNorm (L.greenbaumX *ᵥ y) = 1 := by
  rw [coordNorm_mulVec_eq_of_gram L.greenbaumX
    (leadCols_orthonormal _ L.greenbaum_backward_model.orthonormal)]
  have hsq : coordNorm y ^ 2 = 1 := by rw [coordNorm_sq]; exact hy
  nlinarith [coordNorm_nonneg y]

theorem greenbaum_localization_delta (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y) :
    spectralDistance L.H theta ≤
      L.β k * |y (lastIndex L.hk_pos)| + ‖L.greenbaumDelta‖ := by
  set x := L.greenbaumX *ᵥ y
  have hx : coordNorm x = 1 := L.coordNorm_greenbaumX_mulVec y hy
  have hsplit : L.greenbaumBlockOperator *ᵥ x - theta • x =
      (L.greenbaumTildeA *ᵥ x - theta • x) - L.greenbaumDelta *ᵥ x := by
    rw [greenbaumDelta, Matrix.sub_mulVec]
    abel
  have hres : coordNorm (L.greenbaumBlockOperator *ᵥ x - theta • x) ≤
      L.β k * |y (lastIndex L.hk_pos)| + ‖L.greenbaumDelta‖ := by
    rw [hsplit, L.greenbaum_ritz_residual y theta heig]
    have h1 : coordNorm ((L.β k * y (lastIndex L.hk_pos)) • L.greenbaumVNext) =
        L.β k * |y (lastIndex L.hk_pos)| := by
      have hv : coordNorm L.greenbaumVNext = 1 := by
        have hsq := coordNorm_sq (lastCol L.greenbaumVhat)
        rw [lastCol_dotProduct_self _ L.greenbaum_backward_model.orthonormal] at hsq
        show coordNorm (lastCol L.greenbaumVhat) = 1
        nlinarith [coordNorm_nonneg (lastCol L.greenbaumVhat)]
      rw [coordNorm_smul, hv, mul_one, abs_mul,
        abs_of_nonneg (L.hβ_nonneg k le_rfl)]
    have h2 : coordNorm (L.greenbaumDelta *ᵥ x) ≤ ‖L.greenbaumDelta‖ := by
      have := coordNorm_mulVec_le L.greenbaumDelta x
      rwa [hx, mul_one] at this
    have h3 := coordNorm_add_le ((L.β k * y (lastIndex L.hk_pos)) • L.greenbaumVNext)
      (-(L.greenbaumDelta *ᵥ x))
    have h4 : coordNorm (-(L.greenbaumDelta *ᵥ x)) = coordNorm (L.greenbaumDelta *ᵥ x) := by
      rw [← neg_one_smul ℝ, coordNorm_smul]; simp
    rw [sub_eq_add_neg]
    linarith
  have hdist := spectralDistance_mul_coordNorm_le_blockResidual
    L.ambient_pos L.H L.hHsymm theta x
  rw [hx, mul_one] at hdist
  exact hdist.trans hres

lemma greenbaumDelta_le_of_model :
    ‖L.greenbaumDelta‖ ≤ (480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ := by
  rw [greenbaumDelta, norm_sub_rev]
  exact L.greenbaum_backward_model.perturbation

theorem greenbaum_localization (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y) :
    spectralDistance L.H theta ≤
      L.β k * |y (lastIndex L.hk_pos)| + (480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ := by
  have h := L.greenbaum_localization_delta y theta hy heig
  have hD := L.greenbaumDelta_le_of_model
  linarith

/-- The existential eigenvalue formulation printed in `thm:stabilized`. -/
theorem greenbaum_localization_exists (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y) :
    ∃ i : Fin n,
      |theta - (isHermitian_of_transpose_eq L.hHsymm).eigenvalues i| ≤
        L.β k * |y (lastIndex L.hk_pos)| + (480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ := by
  obtain ⟨i, hi⟩ := exists_eigenvalue_eq_spectralDistance L.ambient_pos
    (isHermitian_of_transpose_eq L.hHsymm) theta
  exact ⟨i, hi.trans_le (L.greenbaum_localization y theta hy heig)⟩

theorem greenbaum_terminal_localization (hterminal : L.β k = 0) (y : Vec k)
    (theta : ℝ) (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y) :
    spectralDistance L.H theta ≤ (480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ := by
  have h := L.greenbaum_localization y theta hy heig
  rw [hterminal, zero_mul, zero_add] at h
  exact h

lemma greenbaumX_transpose_TildeA_X :
    L.greenbaumXᵀ * L.greenbaumTildeA * L.greenbaumX = L.Tmat := by
  rw [Matrix.mul_assoc, L.greenbaum_backward_model.recurrence]
  exact leadCols_transpose_mul_underlineT _ L.greenbaum_backward_model.orthonormal _ _

theorem greenbaum_containment_delta (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y) :
    spectralMin L.H - ‖L.greenbaumDelta‖ ≤ theta ∧
      theta ≤ spectralMax L.H + ‖L.greenbaumDelta‖ := by
  set x := L.greenbaumX *ᵥ y
  have hx : coordNorm x = 1 := L.coordNorm_greenbaumX_mulVec y hy
  have hxx : x ⬝ᵥ x = 1 := by rw [← coordNorm_sq, hx]; norm_num
  have htheta : x ⬝ᵥ (L.greenbaumTildeA *ᵥ x) = theta := by
    have h1 : x ⬝ᵥ (L.greenbaumTildeA *ᵥ x) =
        y ⬝ᵥ ((L.greenbaumXᵀ * L.greenbaumTildeA * L.greenbaumX) *ᵥ y) := by
      simp only [x]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, dotProduct_comm]
    rw [h1, L.greenbaumX_transpose_TildeA_X, heig, dotProduct_smul, smul_eq_mul]
    change theta * vdot y y = theta
    rw [hy, mul_one]
  have hsplit : theta = x ⬝ᵥ (blockDiagonal L.H *ᵥ x) + x ⬝ᵥ (L.greenbaumDelta *ᵥ x) := by
    rw [← htheta, greenbaumDelta, Matrix.sub_mulVec, dotProduct_sub]
    change _ = x ⬝ᵥ (L.greenbaumBlockOperator *ᵥ x) + _
    ring
  have herr : |x ⬝ᵥ (L.greenbaumDelta *ᵥ x)| ≤ ‖L.greenbaumDelta‖ := by
    have h := abs_dotProduct_mulVec_le L.greenbaumDelta x
    rwa [hx, one_pow, mul_one] at h
  have hmax := dotProduct_blockDiagonal_le_spectralMax (k := k + 1)
    L.ambient_pos L.hHsymm x
  have hmin := spectralMin_le_dotProduct_blockDiagonal (k := k + 1)
    L.ambient_pos L.hHsymm x
  rw [hxx, mul_one] at hmax hmin
  have h1 := (abs_le.mp herr).1
  have h2 := (abs_le.mp herr).2
  constructor <;> linarith

theorem greenbaum_containment (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y) :
    spectralMin L.H - (480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ ≤ theta ∧
      theta ≤ spectralMax L.H + (480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ := by
  have h := L.greenbaum_containment_delta y theta hy heig
  have hD := L.greenbaumDelta_le_of_model
  constructor <;> linarith [h.1, h.2]

lemma Tmat_eigenpair (i : Fin k) :
    vdot (⇑((isHermitian_of_transpose_eq L.Tmat_transpose).eigenvectorBasis i))
        (⇑((isHermitian_of_transpose_eq L.Tmat_transpose).eigenvectorBasis i)) = 1 ∧
      L.Tmat *ᵥ
          (⇑((isHermitian_of_transpose_eq L.Tmat_transpose).eigenvectorBasis i)) =
        (isHermitian_of_transpose_eq L.Tmat_transpose).eigenvalues i •
          (⇑((isHermitian_of_transpose_eq L.Tmat_transpose).eigenvectorBasis i)) := by
  let hT := isHermitian_of_transpose_eq L.Tmat_transpose
  refine ⟨?_, hT.mulVec_eigenvectorBasis i⟩
  rw [← vnorm_sq]
  change ‖hT.eigenvectorBasis i‖ ^ 2 = 1
  rw [hT.eigenvectorBasis.orthonormal.1 i]
  norm_num

theorem greenbaum_containment_eigenvalue (i : Fin k) :
    spectralMin L.H - (480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ ≤
        (isHermitian_of_transpose_eq L.Tmat_transpose).eigenvalues i ∧
      (isHermitian_of_transpose_eq L.Tmat_transpose).eigenvalues i ≤
        spectralMax L.H + (480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ :=
  L.greenbaum_containment _ _ (L.Tmat_eigenpair i).1 (L.Tmat_eigenpair i).2

theorem greenbaum_terminal_localization_eigenvalue (hterminal : L.β k = 0)
    (i : Fin k) :
    spectralDistance L.H
        ((isHermitian_of_transpose_eq L.Tmat_transpose).eigenvalues i) ≤
      (480000 * (k : ℝ) ^ 6) * L.ε * ‖L.H‖ :=
  L.greenbaum_terminal_localization hterminal _ _
    (L.Tmat_eigenpair i).1 (L.Tmat_eigenpair i).2

end LanczosRun
end FinitePrecisionLanczos
