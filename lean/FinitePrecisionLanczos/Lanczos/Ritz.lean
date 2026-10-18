import FinitePrecisionLanczos.Lanczos.Assembly
import FinitePrecisionLanczos.Core.Underline


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

def lastIndex (hk : 0 < k) : Fin k := ⟨k - 1, by omega⟩

def rawBoundary : Vec n := L.β k • L.v (k + 1)

def ritzVector (y : Vec k) : Vec n := L.Vmat *ᵥ y

theorem boundary_eq_lastOuter :
    L.boundary = lastOuter L.hk_pos L.rawBoundary := by
  ext i j
  by_cases hlt : j.1 + 1 < k
  · have hj : j ≠ lastIndex L.hk_pos := by
      intro h
      subst j
      change k - 1 + 1 < k at hlt
      omega
    have hcoord : lastCoord L.hk_pos j = 0 := by
      simp only [lastCoord]
      apply Pi.single_eq_of_ne
      intro h
      apply hj
      apply Fin.ext
      simpa [lastIndex] using congrArg Fin.val h
    simp [boundary, hlt, lastOuter, Matrix.vecMulVec, hcoord]
  · have hj : j = lastIndex L.hk_pos := by
      apply Fin.ext
      change j.1 = k - 1
      omega
    subst j
    have hk := L.hk_pos
    have hlast : k - 1 + 1 = k := by omega
    have hnext : k - 1 + 2 = k + 1 := by omega
    simp [boundary, rawBoundary, lastOuter, Matrix.vecMulVec,
      lastCoord, lastIndex, hlast, hnext]


def Vsucc : Mat n (k + 1) := ofCols fun j => L.v (j.1 + 1)

def underlineTmat : Mat (k + 1) k := underlineT L.Tmat (L.β k)

@[simp] lemma leadCols_Vsucc : leadCols L.Vsucc = L.Vmat := rfl

@[simp] lemma lastCol_Vsucc : lastCol L.Vsucc = L.v (k + 1) := rfl

theorem Vsucc_mul_underlineTmat :
    L.Vsucc * L.underlineTmat =
      L.Vmat * L.Tmat + lastOuter L.hk_pos L.rawBoundary := by
  rw [underlineTmat, mul_underlineT L.hk_pos, leadCols_Vsucc, lastCol_Vsucc,
    rawBoundary, lastOuter_smul]

theorem governing : L.H * L.Vmat = L.Vsucc * L.underlineTmat + L.Fmat := by
  rw [L.Vsucc_mul_underlineTmat, ← L.boundary_eq_lastOuter]
  exact L.governing_matrix

lemma boundary_mulVec (y : Vec k) :
    L.boundary *ᵥ y = y (lastIndex L.hk_pos) • L.rawBoundary := by
  ext a
  simp only [Matrix.mulVec, boundary, ofCols, rawBoundary, Pi.smul_apply, smul_eq_mul,
    dotProduct]
  rw [Finset.sum_eq_single (lastIndex L.hk_pos)]
  · have hlast : (lastIndex L.hk_pos).1 + 1 = k := by
      have hk := L.hk_pos
      simp only [lastIndex]
      omega
    have hlast2 : (lastIndex L.hk_pos).1 + 2 = k + 1 := by omega
    have hnot : ¬(lastIndex L.hk_pos).1 + 1 < k := by omega
    simp [hlast, hlast2]
    ring_nf
  · intro j _ hj
    have hlt : j.1 + 1 < k := by
      have hjval : j.1 ≠ k - 1 := by
        intro h
        apply hj
        apply Fin.ext
        simpa [lastIndex] using h
      omega
    simp [hlt]
  · simp

theorem ritz_residual_identity (y : Vec k) (theta : ℝ)
    (heig : L.Tmat *ᵥ y = theta • y) :
    L.H *ᵥ L.ritzVector y - theta • L.ritzVector y =
      y (lastIndex L.hk_pos) • L.rawBoundary + L.Fmat *ᵥ y := by
  have hg := congrArg (fun M : Mat n k => M *ᵥ y) L.governing_matrix
  simp only [Matrix.add_mulVec] at hg
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hg
  rw [heig, L.boundary_mulVec] at hg
  simp only [ritzVector, Matrix.mulVec_smul] at hg ⊢
  rw [hg]
  abel

lemma next_vnorm_le_sqrt (hb : L.β k ≠ 0) :
    vnorm (L.v (k + 1)) ≤ Real.sqrt (1 + L.ε) := by
  have hsq := (abs_le.mp (L.hnext hb)).2
  have hnonneg : 0 ≤ 1 + L.ε := by linarith [L.hε_nonneg]
  have hsqrt : (Real.sqrt (1 + L.ε)) ^ 2 = 1 + L.ε := by
    simpa using Real.sq_sqrt hnonneg
  have hv := vnorm_nonneg (L.v (k + 1))
  have hrs := Real.sqrt_nonneg (1 + L.ε)
  nlinarith

lemma rawBoundary_vnorm_le :
    vnorm L.rawBoundary ≤ Real.sqrt (1 + L.ε) * L.β k := by
  by_cases hb : L.β k = 0
  · simp [rawBoundary, hb, vnorm_zero]
  · rw [rawBoundary, vnorm_smul, abs_of_nonneg (L.hβ_nonneg k le_rfl)]
    calc
      L.β k * vnorm (L.v (k + 1))
          ≤ L.β k * Real.sqrt (1 + L.ε) :=
            mul_le_mul_of_nonneg_left (L.next_vnorm_le_sqrt hb)
              (L.hβ_nonneg k le_rfl)
      _ = Real.sqrt (1 + L.ε) * L.β k := by ring

theorem ritz_residual_bound (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y) :
    vnorm (L.H *ᵥ L.ritzVector y - theta • L.ritzVector y) ≤
      Real.sqrt (1 + L.ε) * L.β k * |y (lastIndex L.hk_pos)| + ‖L.Fmat‖ := by
  rw [L.ritz_residual_identity y theta heig]
  calc
    vnorm (y (lastIndex L.hk_pos) • L.rawBoundary + L.Fmat *ᵥ y)
        ≤ vnorm (y (lastIndex L.hk_pos) • L.rawBoundary)
            + vnorm (L.Fmat *ᵥ y) := vnorm_add_le _ _
    _ ≤ |y (lastIndex L.hk_pos)| *
          (Real.sqrt (1 + L.ε) * L.β k) + ‖L.Fmat‖ * vnorm y := by
      rw [vnorm_smul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left L.rawBoundary_vnorm_le (abs_nonneg _))
        (vnorm_mulVec_le L.Fmat y)
    _ = Real.sqrt (1 + L.ε) * L.β k * |y (lastIndex L.hk_pos)| + ‖L.Fmat‖ := by
      rw [vnorm_eq_one_of_vdot_self y hy, mul_one]
      ring

/-- `eq:ritz-residual-bound`, with the required nonzero-denominator condition. -/
theorem ritz_residual_bound_div (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y)
    (hx : 0 < vnorm (L.ritzVector y)) :
    vnorm (L.H *ᵥ L.ritzVector y - theta • L.ritzVector y) / vnorm (L.ritzVector y) ≤
      (Real.sqrt (1 + L.ε) * L.β k * |y (lastIndex L.hk_pos)| + ‖L.Fmat‖) /
        vnorm (L.ritzVector y) :=
  div_le_div_of_nonneg_right (L.ritz_residual_bound y theta hy heig) hx.le

end LanczosRun
end FinitePrecisionLanczos
