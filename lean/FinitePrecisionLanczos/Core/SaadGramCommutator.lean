import FinitePrecisionLanczos.Core.Underline
import FinitePrecisionLanczos.Core.DilationSaad

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n k : ℕ}

structure SaadGramRecurrence (n k : ℕ) where
  hk : 0 < k
  A : Mat n n
  T : Mat k k
  β : ℝ
  W : Mat n (k + 1)
  Z : Mat n k
  Y : Mat k k
  Γ : Vec k
  hA : Aᵀ = A
  hT : Tᵀ = T
  htri : Tridiagonal T
  hrec : A * leadCols W = W * underlineT T β + Z
  hY : StrictUpper Y
  hgram : (leadCols W)ᵀ * leadCols W = 1 + Yᵀ + Matrix.diagonal Γ + Y

namespace SaadGramRecurrence

variable (G : SaadGramRecurrence n k)

noncomputable def N : Mat k k :=
  G.T * G.Y - G.Y * G.T - G.β • lastOuter G.hk ((leadCols G.W)ᵀ *ᵥ lastCol G.W)

def col (l : Fin (k + 1)) : Vec n := fun a => G.W a l

noncomputable def pi (i : Fin k) : ℝ :=
  underlineT G.T G.β i.succ i * vdot (G.col i.castSucc) (G.col i.succ)

noncomputable def defectJump (i : Fin k) : ℝ :=
  if h : i.1 + 1 < k then |G.T i ⟨i.1 + 1, h⟩ * (G.Γ ⟨i.1 + 1, h⟩ - G.Γ i)| else 0

noncomputable def maxPi : ℝ :=
  Finset.univ.sup' ⟨⟨0, G.hk⟩, Finset.mem_univ _⟩ fun i => |G.pi i|

noncomputable def maxCol : ℝ :=
  Finset.univ.sup' ⟨⟨0, G.hk⟩, Finset.mem_univ _⟩ fun l : Fin k => vnorm (G.col l.castSucc)

noncomputable def maxDefectJump : ℝ :=
  Finset.univ.sup' ⟨⟨0, G.hk⟩, Finset.mem_univ _⟩ G.defectJump

noncomputable def toGram : GramRecurrence n k where
  hk := G.hk
  A := G.A
  T := G.T
  W := leadCols G.W
  b := G.β • lastCol G.W
  Z := G.Z
  Y := G.Y
  Δ := G.Γ
  hA := G.hA
  hT := G.hT
  htri := G.htri
  hrec := by rw [G.hrec, mul_underlineT G.hk, lastOuter_smul]
  hY := G.hY
  hgram := G.hgram

theorem N_eq : G.N = G.toGram.N := by
  rw [N, GramRecurrence.N]
  simp only [toGram, Matrix.mulVec_smul, lastOuter_smul]

lemma toGram_col (l : Fin k) : G.toGram.col l = G.col l.castSucc := rfl

lemma pi_eq (i : Fin k) : G.pi i = G.toGram.pi i := by
  unfold pi GramRecurrence.pi
  rw [underlineT_succ_self]
  by_cases h : i.1 + 1 < k
  · simp only [dif_pos h, toGram_col]
    rw [G.toGram.T_symm]
    rfl
  · simp only [dif_neg h, toGram_col]
    have hi : i.succ = Fin.last k := Fin.ext (by simp; omega)
    simp [toGram, hi, vdot, dotProduct_smul]
    left
    rfl

lemma maxPi_eq : G.maxPi = G.toGram.maxPi := by
  simp only [maxPi, GramRecurrence.maxPi, G.pi_eq]

lemma maxCol_eq : G.maxCol = G.toGram.maxCol := rfl

lemma maxDefectJump_eq : G.maxDefectJump = G.toGram.maxDefectJump := rfl

/-- The leading strict upper triangle agrees with the given Gram decomposition. -/
lemma strictUpperPart_eq : strictUpperPart ((leadCols G.W)ᵀ * leadCols G.W) = G.Y := by
  ext i j
  by_cases hij : i.1 < j.1
  · have hne : i ≠ j := by intro h; subst j; omega
    have hji : G.Y j i = 0 := G.hY j i (by omega)
    simp [strictUpperPart, G.hgram, hij, Matrix.one_apply, Matrix.diagonal_apply, hne, hji]
  · simp [strictUpperPart, hij, G.hY i j (by omega)]

/-- The generic commutator in its rectangular, zero-padded paper form. -/
theorem padded_commutator :
    underlineT G.T G.β * G.Y - strictUpperPart (G.Wᵀ * G.W) * underlineT G.T G.β =
      padRow G.N := by
  apply saad_commutator_block G.hk G.T G.β (strictUpperPart (G.Wᵀ * G.W)) G.Y
    ((leadCols G.W)ᵀ *ᵥ lastCol G.W) G.hY
  · rw [leadBlock_strictUpperPart_gram, G.strictUpperPart_eq]
  · exact strictUpperPart_gram_castSucc_last G.W
  · exact strictUpperPart_last _

theorem N_skew :
    G.N - G.Nᵀ = (leadCols G.W)ᵀ * G.Z - G.Zᵀ * leadCols G.W -
      (G.T * Matrix.diagonal G.Γ - Matrix.diagonal G.Γ * G.T) := by
  rw [N_eq]
  exact G.toGram.N_skew

theorem N_upper : Upper G.N := by
  rw [N_eq]
  exact G.toGram.N_upper

theorem N_norm_bound (P c D : ℝ) (hpi : ∀ i, |G.pi i| ≤ P)
    (hcol : ∀ l : Fin k, vnorm (G.col l.castSucc) ≤ c)
    (hΓ : ∀ i j : Fin k, i.1 + 1 = j.1 → |G.T i j * (G.Γ j - G.Γ i)| ≤ D)
    (hD : 0 ≤ D) :
    ‖G.N‖ ≤ (k : ℝ) * max (2 * P) (2 * c * ‖G.Z‖ + D) := by
  rw [N_eq]
  refine G.toGram.N_norm_bound P c D ?_ ?_ hcol hΓ hD
  · intro i j hij
    have hi : i.1 + 1 < k := hij ▸ j.2
    have hj : j = ⟨i.1 + 1, hi⟩ := Fin.ext hij.symm
    subst hj
    have h := hpi i
    rw [G.pi_eq] at h
    simpa only [GramRecurrence.pi, dif_pos hi] using h
  · intro i hi
    have h := hpi i
    rw [G.pi_eq] at h
    simpa only [GramRecurrence.pi, dif_neg (show ¬i.1 + 1 < k by omega)] using h

theorem gram_commutator :
    Upper G.N ∧
      ‖G.N‖ ≤ 2 * (k : ℝ) * (G.maxPi + G.maxCol * ‖G.Z‖ + G.maxDefectJump) := by
  refine ⟨G.N_upper, ?_⟩
  rw [N_eq, maxPi_eq, maxCol_eq, maxDefectJump_eq]
  exact G.toGram.gram_commutator_bound

end SaadGramRecurrence
end FinitePrecisionLanczos
