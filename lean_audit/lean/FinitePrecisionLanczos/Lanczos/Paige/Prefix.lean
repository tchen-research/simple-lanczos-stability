import FinitePrecisionLanczos.Lanczos.Paige.Ritz










namespace FinitePrecisionLanczos

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)


def take (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k) : LanczosRun n t where
  H := L.H
  v := L.v
  u := L.u
  w := L.w
  z := L.z
  α := L.α
  β := L.β
  eu := L.eu
  ew := L.ew
  ez := L.ez
  eα := L.eα
  Δ := L.Δ
  ε := L.ε
  hHsymm := L.hHsymm
  hε_nonneg := L.hε_nonneg
  hk_pos := ht0
  hsmall := by
    have ht : (t : ℝ) ≤ k := by exact_mod_cast htk
    have he := L.hε_nonneg
    calc
      (t : ℝ) * L.ε ≤ (k : ℝ) * L.ε := mul_le_mul_of_nonneg_right ht he
      _ ≤ 1 / 100 := L.hsmall
  hv_zero := L.hv_zero
  hβ_zero := L.hβ_zero
  h_u := fun j hj => L.h_u j (lt_of_lt_of_le hj htk)
  heu := fun j hj => L.heu j (lt_of_lt_of_le hj htk)
  h_w := fun j hj => L.h_w j (lt_of_lt_of_le hj htk)
  hew := fun j hj => L.hew j (lt_of_lt_of_le hj htk)
  h_al := fun j hj => L.h_al j (lt_of_lt_of_le hj htk)
  heal := fun j hj => L.heal j (lt_of_lt_of_le hj htk)
  h_z := fun j hj => L.h_z j (lt_of_lt_of_le hj htk)
  hez := fun j hj => L.hez j (lt_of_lt_of_le hj htk)
  h_be := fun j hj => L.h_be j (lt_of_lt_of_le hj htk)
  hΔ := fun j hj => L.hΔ j (lt_of_lt_of_le hj htk)
  hnear := fun j hj1 hjt => L.hnear j hj1 (hjt.trans htk)
  hnext := by
    intro hb
    by_cases htk' : t = k
    · subst t
      exact L.hnext hb
    · exact L.hnear (t + 1) (by omega) (by omega)
  hβ_nonneg := fun j hjt => L.hβ_nonneg j (hjt.trans htk)
  hβ_internal := fun j hj1 hjt => L.hβ_internal j hj1 (lt_of_lt_of_le hjt htk)

@[simp] lemma take_H (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k) :
    (L.take t ht0 htk).H = L.H := rfl

@[simp] lemma take_v (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k) :
    (L.take t ht0 htk).v = L.v := rfl

@[simp] lemma take_alpha (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k) :
    (L.take t ht0 htk).α = L.α := rfl

@[simp] lemma take_beta (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k) :
    (L.take t ht0 htk).β = L.β := rfl

@[simp] lemma take_epsilon (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k) :
    (L.take t ht0 htk).ε = L.ε := rfl

end LanczosRun
end FinitePrecisionLanczos
