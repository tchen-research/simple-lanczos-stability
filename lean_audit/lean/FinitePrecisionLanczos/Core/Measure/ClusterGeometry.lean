import FinitePrecisionLanczos.Core.Measure.Cutoff










namespace FinitePrecisionLanczos

open Set


def clusterNeighborhood {I : Type*} (x : I → ℝ)
    (G : ℝ → Prop) (delta : ℝ) : Set ℝ :=
  {t | ∃ i, G (x i) ∧ |t - x i| ≤ delta}


def twoAtomicSupports {I J : Type*} (x : I → ℝ) (y : J → ℝ) : Set ℝ :=
  Set.range x ∪ Set.range y




lemma physical_mem_clusterNeighborhood_iff
    {I : Type*} (x : I → ℝ) (G : ℝ → Prop)
    (delta g : ℝ) (hdelta : 0 ≤ delta) (hsmall : 2 * delta < g)
    (hgap : ∀ i j,
      (G (x i) ∧ ¬G (x j)) ∨ (¬G (x i) ∧ G (x j)) →
        g ≤ |x i - x j|) (i : I) :
    x i ∈ clusterNeighborhood x G delta ↔ G (x i) := by
  constructor
  · rintro ⟨j, hGj, hdist⟩
    by_contra hGi
    have hgapij := hgap j i (Or.inl ⟨hGj, hGi⟩)
    rw [abs_sub_comm] at hgapij
    linarith
  · intro hGi
    exact ⟨i, hGi, by simpa using hdelta⟩



theorem clusterNeighborhood_separation
    {I J : Type*} (x : I → ℝ) (y : J → ℝ)
    (G : ℝ → Prop) (delta g : ℝ)
    (hdelta : 0 ≤ delta) (hsmall : 2 * delta < g)
    (hgap : ∀ i j,
      (G (x i) ∧ ¬G (x j)) ∨ (¬G (x i) ∧ G (x j)) →
        g ≤ |x i - x j|)
    (hloc : ∀ j, ∃ i, |y j - x i| ≤ delta) :
    ∀ z ∈ twoAtomicSupports x y, ∀ w ∈ twoAtomicSupports x y,
      (z ∈ clusterNeighborhood x G delta ∧
          w ∉ clusterNeighborhood x G delta) ∨
        (z ∉ clusterNeighborhood x G delta ∧
          w ∈ clusterNeighborhood x G delta) →
      g - 2 * delta ≤ |z - w| := by
  have hphysical := physical_mem_clusterNeighborhood_iff
    x G delta g hdelta hsmall hgap
  have hforward : ∀ z ∈ twoAtomicSupports x y,
      z ∈ clusterNeighborhood x G delta →
      ∀ w ∈ twoAtomicSupports x y,
        w ∉ clusterNeighborhood x G delta →
        g - 2 * delta ≤ |z - w| := by
    intro z hzS hzP w hwS hwP
    obtain ⟨i, hGi, hzi⟩ := hzP
    have hout : ∃ j, ¬G (x j) ∧ |w - x j| ≤ delta := by
      rcases hwS with hwx | hwy
      · obtain ⟨j, rfl⟩ := hwx
        have hnotG : ¬G (x j) := by
          intro hGj
          exact hwP ((hphysical j).mpr hGj)
        exact ⟨j, hnotG, by simpa using hdelta⟩
      · obtain ⟨j, rfl⟩ := hwy
        obtain ⟨ell, hjell⟩ := hloc j
        have hnotG : ¬G (x ell) := by
          intro hGell
          exact hwP ⟨ell, hGell, hjell⟩
        exact ⟨ell, hnotG, hjell⟩
    obtain ⟨j, hGj, hwj⟩ := hout
    have hgapij := hgap i j (Or.inl ⟨hGi, hGj⟩)
    have htri : |x i - x j| ≤ |x i - z| + |z - w| + |w - x j| := by
      calc
        |x i - x j| = |(x i - z) + (z - w) + (w - x j)| := by ring_nf
        _ ≤ |x i - z| + |z - w| + |w - x j| := by
          exact (abs_add_le ((x i - z) + (z - w)) (w - x j)).trans
            (add_le_add (abs_add_le (x i - z) (z - w)) le_rfl)
    rw [abs_sub_comm (x i) z] at htri
    linarith
  intro z hzS w hwS hcross
  rcases hcross with hzw | hwz
  · exact hforward z hzS hzw.1 w hwS hzw.2
  · rw [abs_sub_comm]
    exact hforward w hwS hwz.2 z hzS hwz.1

end FinitePrecisionLanczos
