import FinitePrecisionLanczos.Core.Measure.ClusterGeometry
import FinitePrecisionLanczos.Lanczos.Greenbaum.Wasserstein









namespace FinitePrecisionLanczos

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace LanczosRun.GreenbaumModel

variable {n k : ℕ} (L : LanczosRun n k) (M : L.GreenbaumModel)


noncomputable def physicalEigenvalue (i : Fin n) : ℝ :=
  (isHermitian_of_transpose_eq L.hHsymm).eigenvalues i


noncomputable def modelEigenvalue (j : Fin k ⊕ Fin M.d) : ℝ :=
  (indexed_isHermitian_of_transpose_eq M.Ttilde_symmetric).eigenvalues j


noncomputable def physicalSpectralWeight (i : Fin n) : ℝ :=
  ((⇑((isHermitian_of_transpose_eq L.hHsymm).eigenvectorBasis i) ⬝ᵥ
      L.normalizedStart) ^ 2)


noncomputable def modelSpectralWeight (j : Fin k ⊕ Fin M.d) : ℝ :=
  ((⇑((indexed_isHermitian_of_transpose_eq M.Ttilde_symmetric).eigenvectorBasis j) ⬝ᵥ
      completionFirst L.hk_pos M.d) ^ 2)



theorem starting_cluster_mass_product
    (G C : ℝ → Prop) [DecidablePred G] [DecidablePred C]
    (g : ℝ)
    (hC : ∀ t, C t ↔
      t ∈ clusterNeighborhood (physicalEigenvalue L) G M.delta)
    (hgap : ∀ i j,
      (G (physicalEigenvalue L i) ∧ ¬G (physicalEigenvalue L j)) ∨
        (¬G (physicalEigenvalue L i) ∧ G (physicalEigenvalue L j)) →
      g ≤ |physicalEigenvalue L i - physicalEigenvalue L j|)
    (hsmall : 2 * M.delta < g) :
    (g - 2 * M.delta) *
        |finiteGroupMass (physicalSpectralWeight L)
              (physicalEigenvalue L) G -
          finiteGroupMass (modelSpectralWeight L M)
              (modelEigenvalue L M) C| ≤
      Real.sqrt (n * k) * M.delta := by
  classical
  let x : Fin n → ℝ := physicalEigenvalue L
  let y : Fin k ⊕ Fin M.d → ℝ := modelEigenvalue L M
  let source : Fin n → ℝ := physicalSpectralWeight L
  let target : Fin k ⊕ Fin M.d → ℝ := modelSpectralWeight L M
  let S : Set ℝ := twoAtomicSupports x y
  let P : Set ℝ := clusterNeighborhood x G M.delta
  have hdelta : 0 ≤ M.delta := norm_nonneg _
  have hr : 0 ≤ g - 2 * M.delta := by linarith
  have hloc : ∀ j, ∃ i, |y j - x i| ≤ M.delta := by
    intro j
    obtain ⟨i, hi⟩ := exists_eigenvalue_abs_eq_spectralDistance
      L.ambient_pos (isHermitian_of_transpose_eq L.hHsymm) (y j)
    refine ⟨i, ?_⟩
    change |y j - (isHermitian_of_transpose_eq L.hHsymm).eigenvalues i| ≤ M.delta
    rw [hi]
    exact eigenvalue_localization L M j
  have hxS : ∀ i, x i ∈ S := by
    intro i
    exact Or.inl ⟨i, rfl⟩
  have hyS : ∀ j, y j ∈ S := by
    intro j
    exact Or.inr ⟨j, rfl⟩
  have hxP : ∀ i, x i ∈ P ↔ G (x i) := by
    intro i
    exact physical_mem_clusterNeighborhood_iff
      x G M.delta g hdelta hsmall hgap i
  have hyP : ∀ j, y j ∈ P ↔ C (y j) := by
    intro j
    exact (hC (y j)).symm
  have hsep : ∀ z ∈ S, ∀ w ∈ S,
      (z ∈ P ∧ w ∉ P) ∨ (z ∉ P ∧ w ∈ P) →
        g - 2 * M.delta ≤ |z - w| := by
    exact clusterNeighborhood_separation
      x y G M.delta g hdelta hsmall hgap hloc
  have htest : ∀ f : ℝ → ℝ, OneLipschitz f →
      |atomicIntegral (indexedAtomicMass source x) f -
        atomicIntegral (indexedAtomicMass target y) f| ≤
          Real.sqrt (n * k) * M.delta := by
    intro f hf
    have hcard : Fintype.card (Fin k ⊕ Fin M.d) = n * k := by
      simpa [Nat.mul_comm] using M.dimension.symm
    have hpert := spectralIntegral_lipschitz_sub_le M.S M.Ttilde
      (indexed_isHermitian_of_transpose_eq M.S_symmetric)
      (indexed_isHermitian_of_transpose_eq M.Ttilde_symmetric)
      (completionFirst L.hk_pos M.d)
      (coordNorm_completionFirst L.hk_pos) f hf
    rw [M.starting_spectralMass] at hpert
    simpa [source, target, x, y, physicalSpectralWeight,
      modelSpectralWeight, physicalEigenvalue, modelEigenvalue,
      spectralMass, indexedAtomicMass, GreenbaumModel.delta, hcard] using hpert
  simpa [source, target, x, y] using
    finiteGroupMass_cutoff_bound source target x y G C S P
      hxS hyS hxP hyP (g - 2 * M.delta)
      (Real.sqrt (n * k) * M.delta) hr hsep htest




theorem starting_cluster_mass
    (G C : ℝ → Prop) [DecidablePred G] [DecidablePred C]
    (g : ℝ)
    (hC : ∀ t, C t ↔
      t ∈ clusterNeighborhood (physicalEigenvalue L) G M.delta)
    (hgap : ∀ i j,
      (G (physicalEigenvalue L i) ∧ ¬G (physicalEigenvalue L j)) ∨
        (¬G (physicalEigenvalue L i) ∧ G (physicalEigenvalue L j)) →
      g ≤ |physicalEigenvalue L i - physicalEigenvalue L j|)
    (hsmall : 2 * M.delta < g) :
    |finiteGroupMass (physicalSpectralWeight L)
          (physicalEigenvalue L) G -
      finiteGroupMass (modelSpectralWeight L M)
          (modelEigenvalue L M) C| ≤
      (Real.sqrt (n * k) * M.delta) / (g - 2 * M.delta) := by
  have hpos : 0 < g - 2 * M.delta := by linarith
  apply (le_div_iff₀ hpos).2
  simpa [mul_comm] using
    (starting_cluster_mass_product L M G C g hC hgap hsmall)

end LanczosRun.GreenbaumModel
end FinitePrecisionLanczos
