import FinitePrecisionLanczos.Lanczos.Paige.LossBounds









namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)



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
      have hs := vnorm_sq y
      have hv : vnorm y = 1 := by
        rw [hy] at hs
        nlinarith [vnorm_nonneg y]
      rw [hv, mul_one]
      ring



theorem loss_orthogonality_dichotomy (y : Vec k) (theta : ℝ)
    (hy : vdot y y = 1) (heig : L.Tmat *ᵥ y = theta • y)
    (hpos : 0 < L.β k * |y (lastIndex L.hk_pos)|) :
    |vdot (L.ritzVector y) (L.v (k + 1))| ≤
      ((6000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖) /
        (L.β k * |y (lastIndex L.hk_pos)|) := by
  have hp := L.paige_bound y theta hy heig
  rw [rawBoundary, vdot, dotProduct_smul, smul_eq_mul, abs_mul,
    abs_mul, abs_of_nonneg (L.hβ_nonneg k le_rfl)] at hp
  apply (le_div_iff₀ hpos).2
  change |L.ritzVector y ⬝ᵥ L.v (k + 1)| *
      (L.β k * |y (lastIndex L.hk_pos)|) ≤
        (6000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖
  nlinarith [hp]

end LanczosRun
end FinitePrecisionLanczos
