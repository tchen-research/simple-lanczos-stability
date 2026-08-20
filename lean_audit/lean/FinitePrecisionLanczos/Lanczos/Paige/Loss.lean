import FinitePrecisionLanczos.Lanczos.Paige.Commutator








namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)


def lastIndex (hk : 0 < k) : Fin k := ⟨k - 1, by omega⟩


def rawBoundary : Vec n := L.β k • L.v (k + 1)



def ritzVector (y : Vec k) : Vec n := L.Vmat *ᵥ y



def eta (y : Vec k) : ℝ :=
  -vdot y (L.upG *ᵥ y) + vdot y (L.upQ *ᵥ y)


def paigeSum (y : Vec k) : ℝ :=
  ∑ j : Fin k, (y j) ^ 2 * (L.p (j.1 + 1) - L.p j.1)


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



lemma Cmat_quadratic (y : Vec k) :
    vdot y (L.Cmat *ᵥ y)
      = vdot (L.ritzVector y) L.rawBoundary * y (lastIndex L.hk_pos) := by
  have hadjoint : vdot y (L.Cmat *ᵥ y)
      = vdot (L.Vmat *ᵥ y) (L.boundary *ᵥ y) := by
    simp only [vdot, Cmat]
    rw [← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_transpose_mulVec]
    exact dotProduct_comm _ _
  rw [hadjoint, L.boundary_mulVec]
  simp [ritzVector, rawBoundary, vdot, dotProduct_smul, smul_eq_mul]
  ring


lemma Nmat_quadratic (y : Vec k) :
    -(vdot y (L.Nmat *ᵥ y)) = L.paigeSum y := by
  have hdiag := Core.dotProduct_diagonal_mulVec
    (fun j : Fin k => L.p j.1 - L.p (j.1 + 1)) y
  change -(y ⬝ᵥ ((Matrix.diagonal (fun j : Fin k =>
      L.p j.1 - L.p (j.1 + 1))) *ᵥ y)) = L.paigeSum y
  rw [hdiag]
  simp only [paigeSum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring



theorem paige_identity (y : Vec k) (theta : ℝ)
    (heig : L.Tmat *ᵥ y = theta • y) :
    vdot (L.ritzVector y) L.rawBoundary * y (lastIndex L.hk_pos)
      = L.paigeSum y + L.eta y := by
  have hupper : L.Tmat * L.Rmat - L.Rmat * L.Tmat
      = L.Cmat + L.Nmat + (L.upG - L.upQ) := by
    simpa [Amat, sub_eq_add_neg, add_assoc] using L.upper_commutator
  have hs := Core.paige_sandwich L.Tmat L.Rmat L.Cmat L.Nmat
    (L.upG - L.upQ) L.Tmat_transpose y theta heig hupper
  change vdot y (L.Cmat *ᵥ y) =
    -(vdot y (L.Nmat *ᵥ y)) - vdot y ((L.upG - L.upQ) *ᵥ y) at hs
  rw [L.Cmat_quadratic] at hs
  have hN := L.Nmat_quadratic y
  simp only [vdot, Matrix.sub_mulVec, dotProduct_sub] at hs
  simp only [paigeSum, eta, vdot] at hN ⊢
  linarith

end LanczosRun
end FinitePrecisionLanczos
