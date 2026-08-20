import FinitePrecisionLanczos.Core.Descent









namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator


def prefixLength {t : ℕ} (s : Fin (t - 1)) : ℕ := s.1 + 1

lemma prefixLength_pos {t : ℕ} (s : Fin (t - 1)) : 0 < prefixLength s := by
  simp [prefixLength]

lemma prefixLength_lt {t : ℕ} (s : Fin (t - 1)) : prefixLength s < t := by
  simp only [prefixLength]
  omega


def leadingVector {t : ℕ} (y : Vec t) (s : Fin (t - 1)) : Vec (prefixLength s) :=
  fun i => y ⟨i.1, lt_trans i.2 (prefixLength_lt s)⟩


def afterPrefix {t : ℕ} (y : Vec t) (s : Fin (t - 1)) : ℝ :=
  y ⟨prefixLength s, prefixLength_lt s⟩


def prefixLastBasis {t : ℕ} (s : Fin (t - 1)) : Vec (prefixLength s) :=
  fun i => if i.1 + 1 = prefixLength s then 1 else 0

@[simp] lemma prefixLastBasis_dot {t : ℕ} (s : Fin (t - 1))
    (y : Vec (prefixLength s)) :
    vdot y (prefixLastBasis s) = y ⟨prefixLength s - 1, by
      have := prefixLength_pos s
      omega⟩ := by
  simp only [vdot, dotProduct, prefixLastBasis, mul_ite, mul_one, mul_zero]
  let last : Fin (prefixLength s) := ⟨prefixLength s - 1, by
    have := prefixLength_pos s
    omega⟩
  rw [Finset.sum_eq_single last]
  · simp [last]
    have : prefixLength s - 1 + 1 = prefixLength s := by
      have := prefixLength_pos s
      omega
    simp [this]
  · intro i _ hilast
    have hne : ¬i.1 + 1 = prefixLength s := by
      intro h
      apply hilast
      apply Fin.ext
      dsimp [last]
      omega
    simp [hne]
  · simp

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)


def descentPrefix (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (s : Fin (t - 1)) : LanczosRun n (prefixLength s) :=
  L.take (prefixLength s) (prefixLength_pos s)
    ((prefixLength_lt s).le.trans htk)


noncomputable def prefixHermitian (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (s : Fin (t - 1)) : (L.descentPrefix t ht0 htk s).Tmat.IsHermitian :=
  isHermitian_of_transpose_eq (L.descentPrefix t ht0 htk s).Tmat_transpose


noncomputable def prefixEigenvalue (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (s : Fin (t - 1)) (r : Fin (prefixLength s)) : ℝ :=
  (L.prefixHermitian t ht0 htk s).eigenvalues r


noncomputable def prefixEigenvector (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (s : Fin (t - 1)) (r : Fin (prefixLength s)) : Vec (prefixLength s) :=
  ⇑((L.prefixHermitian t ht0 htk s).eigenvectorBasis r)

lemma prefixEigenvector_unit (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (s : Fin (t - 1)) (r : Fin (prefixLength s)) :
    vdot (L.prefixEigenvector t ht0 htk s r)
      (L.prefixEigenvector t ht0 htk s r) = 1 := by
  rw [← vnorm_sq]
  change ‖(L.prefixHermitian t ht0 htk s).eigenvectorBasis r‖ ^ 2 = 1
  rw [(L.prefixHermitian t ht0 htk s).eigenvectorBasis.orthonormal.1 r]
  norm_num

lemma prefixEigenvector_equation (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (s : Fin (t - 1)) (r : Fin (prefixLength s)) :
    (L.descentPrefix t ht0 htk s).Tmat *ᵥ
      L.prefixEigenvector t ht0 htk s r =
        L.prefixEigenvalue t ht0 htk s r •
          L.prefixEigenvector t ht0 htk s r := by
  exact (L.prefixHermitian t ht0 htk s).mulVec_eigenvectorBasis r


theorem leading_rows (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (s : Fin (t - 1)) (y : Vec t) (theta : ℝ)
    (heig : (L.take t ht0 htk).Tmat *ᵥ y = theta • y) :
    (L.descentPrefix t ht0 htk s).Tmat *ᵥ leadingVector y s =
      theta • leadingVector y s -
        (L.β (prefixLength s) * afterPrefix y s) • prefixLastBasis s := by
  ext i
  let it : Fin t := ⟨i.1, lt_trans i.2 (prefixLength_lt s)⟩
  have heig_i := congrFun heig it
  rw [(L.take t ht0 htk).Tmat_mulVec_apply y it] at heig_i
  simp only [take_alpha, take_beta, Pi.smul_apply, smul_eq_mul] at heig_i
  change
    (L.α (i.1 + 1) * y it +
      (if hi : i.1 = 0 then 0 else L.β i.1 * y ⟨i.1 - 1, by
        exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_trans i.2 (prefixLength_lt s))⟩) +
      (if hi : i.1 + 1 < t then L.β (i.1 + 1) * y ⟨i.1 + 1, hi⟩ else 0)) =
      theta * y it at heig_i
  rw [(L.descentPrefix t ht0 htk s).Tmat_mulVec_apply (leadingVector y s) i]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, descentPrefix,
    take_alpha, take_beta]
  have hcur : leadingVector y s i = y it := rfl
  have hprev :
      (if hi : i.1 = 0 then 0
        else L.β i.1 * leadingVector y s ⟨i.1 - 1, by omega⟩) =
      (if hi : it.1 = 0 then 0
        else L.β it.1 * y ⟨it.1 - 1, by omega⟩) := by
    by_cases hi : i.1 = 0
    · simp [hi, it]
    · simp only [hi, it, ↓reduceDIte]
      congr 2
  by_cases hlast : i.1 + 1 = prefixLength s
  · have hnotSucc : ¬i.1 + 1 < prefixLength s := by omega
    have hiT : i.1 + 1 < t := by
      rw [hlast]
      exact prefixLength_lt s
    have htail :
        y ⟨i.1 + 1, hiT⟩ = afterPrefix y s := by
      apply congrArg y
      apply Fin.ext
      simpa [afterPrefix] using hlast
    simp only [hiT, ↓reduceDIte] at heig_i
    simp only [it] at hprev
    rw [show L.α (i.1 + 1) = L.α (prefixLength s) by rw [hlast],
      show L.β (i.1 + 1) = L.β (prefixLength s) by rw [hlast]] at heig_i
    simp only [hnotSucc, ↓reduceDIte]
    rw [hcur, hprev]
    simp only [prefixLastBasis, hlast, if_pos, mul_one]
    rw [htail] at heig_i
    linarith
  · have hsucc : i.1 + 1 < prefixLength s := by omega
    have hiT : i.1 + 1 < t := lt_trans hsucc (prefixLength_lt s)
    have hsuccVal :
        leadingVector y s ⟨i.1 + 1, hsucc⟩ =
          y ⟨it.1 + 1, by simpa [it] using hiT⟩ := by
      apply congrArg y
      apply Fin.ext
      rfl
    simp only [hiT, ↓reduceDIte] at heig_i
    simp only [hsucc, ↓reduceDIte]
    rw [hcur, hprev, hsuccVal]
    simp [prefixLastBasis, hlast]
    exact heig_i


theorem leading_coefficient (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (s : Fin (t - 1)) (r : Fin (prefixLength s))
    (y : Vec t) (theta : ℝ)
    (heig : (L.take t ht0 htk).Tmat *ᵥ y = theta • y) :
    (theta - L.prefixEigenvalue t ht0 htk s r) *
        vdot (L.prefixEigenvector t ht0 htk s r) (leadingVector y s) =
      L.β (prefixLength s) *
        (L.prefixEigenvector t ht0 htk s r)
          ⟨prefixLength s - 1, by
            have := prefixLength_pos s
            omega⟩ * afterPrefix y s := by
  have hcore := Core.coeff_product
    (L.descentPrefix t ht0 htk s).Tmat
    (L.descentPrefix t ht0 htk s).Tmat_transpose
    (leadingVector y s) (prefixLastBasis s)
    (L.prefixEigenvector t ht0 htk s r)
    theta (L.prefixEigenvalue t ht0 htk s r)
    (L.β (prefixLength s) * afterPrefix y s)
    (L.leading_rows t ht0 htk s y theta heig)
    (L.prefixEigenvector_equation t ht0 htk s r)
  have hlastdot := prefixLastBasis_dot s
    (L.prefixEigenvector t ht0 htk s r)
  change (theta - L.prefixEigenvalue t ht0 htk s r) *
      vdot (L.prefixEigenvector t ht0 htk s r) (leadingVector y s) =
    (L.β (prefixLength s) * afterPrefix y s) *
      vdot (L.prefixEigenvector t ht0 htk s r) (prefixLastBasis s) at hcore
  rw [hlastdot] at hcore
  simpa [vdot, mul_assoc, mul_left_comm, mul_comm] using hcore



noncomputable def descentGap (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (theta : ℝ) (s : Fin (t - 1)) (r : Fin (prefixLength s)) : ℝ :=
  theta - L.prefixEigenvalue t ht0 htk s r

noncomputable def descentEdge (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (s : Fin (t - 1)) (r : Fin (prefixLength s)) : ℝ :=
  L.β (prefixLength s) *
    L.prefixEigenvector t ht0 htk s r
      ⟨prefixLength s - 1, by
        have := prefixLength_pos s
        omega⟩

noncomputable def descentCoeff (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (y : Vec t) (s : Fin (t - 1)) (r : Fin (prefixLength s)) : ℝ :=
  vdot (L.prefixEigenvector t ht0 htk s r) (leadingVector y s)

noncomputable def descentCorr (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (s : Fin (t - 1)) (r : Fin (prefixLength s)) : ℝ :=
  vdot ((L.descentPrefix t ht0 htk s).ritzVector
      (L.prefixEigenvector t ht0 htk s r))
    (L.v (prefixLength s + 1))

def descentTail {t : ℕ} (y : Vec t) (s : Fin (t - 1)) : ℝ :=
  afterPrefix y s



theorem descent_coefficient_identity (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (y : Vec t) (theta : ℝ)
    (heig : (L.take t ht0 htk).Tmat *ᵥ y = theta • y)
    (s : Fin (t - 1)) (r : Fin (prefixLength s)) :
    L.descentGap t ht0 htk theta s r * L.descentCoeff t ht0 htk y s r =
      L.descentEdge t ht0 htk s r * descentTail y s := by
  simpa [descentGap, descentCoeff, descentEdge, descentTail, mul_assoc] using
    L.leading_coefficient t ht0 htk s r y theta heig



theorem leading_paige_product_bound (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (s : Fin (t - 1)) (r : Fin (prefixLength s)) :
    |L.descentEdge t ht0 htk s r * L.descentCorr t ht0 htk s r| ≤
      (6000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by
  let P := L.descentPrefix t ht0 htk s
  let yr := L.prefixEigenvector t ht0 htk s r
  let thetar := L.prefixEigenvalue t ht0 htk s r
  have hp := P.paige_bound yr thetar
    (L.prefixEigenvector_unit t ht0 htk s r)
    (L.prefixEigenvector_equation t ht0 htk s r)
  have hlenk : prefixLength s ≤ k :=
    (prefixLength_lt s).le.trans htk
  have hlenR : ((prefixLength s : ℕ) : ℝ) ≤ k := by exact_mod_cast hlenk
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hscale : 0 ≤ L.ε * ‖L.H‖ :=
    mul_nonneg L.hε_nonneg (norm_nonneg _)
  have hcubes : ((prefixLength s : ℕ) : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hlenR 3
  have hlast : lastIndex P.hk_pos =
      ⟨prefixLength s - 1, by
        have := prefixLength_pos s
        omega⟩ := by
    apply Fin.ext
    simp [lastIndex, P, descentPrefix]
  rw [hlast] at hp
  have hp' :
      |L.descentEdge t ht0 htk s r * L.descentCorr t ht0 htk s r| ≤
        (6000 * ((prefixLength s : ℕ) : ℝ) ^ 3) * L.ε * ‖L.H‖ := by
    simpa [P, yr, thetar, descentPrefix, descentEdge, descentCorr, rawBoundary,
      ritzVector, vdot, dotProduct_smul, smul_eq_mul, abs_mul,
      abs_of_nonneg (L.hβ_nonneg (prefixLength s) hlenk),
      mul_assoc, mul_left_comm, mul_comm] using hp
  calc
    |L.descentEdge t ht0 htk s r * L.descentCorr t ht0 htk s r|
        ≤ (6000 * ((prefixLength s : ℕ) : ℝ) ^ 3) * L.ε * ‖L.H‖ := hp'
    _ ≤ (6000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖ := by
      nlinarith



theorem rho_expansion_physical (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (y : Vec t) :
    vdot y ((L.take t ht0 htk).Rmat *ᵥ y) =
      ∑ s : Fin (t - 1),
        vdot ((L.descentPrefix t ht0 htk s).ritzVector (leadingVector y s))
          (L.v (prefixLength s + 1)) * descentTail y s := by
  let P := L.take t ht0 htk
  let term : Fin t → Fin t → ℝ := fun i j =>
    y i * vdot (L.v (i.1 + 1)) (L.v (j.1 + 1)) * y j
  have hleft :
      vdot y (P.Rmat *ᵥ y) =
        ∑ i : Fin t, ∑ j : Fin t,
          if i.1 < j.1 then term i j else 0 := by
    simp only [vdot, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i.1 < j.1
    · have hne : i ≠ j := by intro h; simpa [h] using hij.ne
      simp [P, Rmat, hij, LanczosRun.Omega_offdiag, hne, term, take_v]
      ring
    · simp [P, Rmat, hij]
  rw [hleft, strictUpper_sum_by_columns term]
  apply Finset.sum_congr rfl
  intro s _
  simp only [term, descentTail, afterPrefix]
  have hritz :
      vdot ((L.descentPrefix t ht0 htk s).ritzVector (leadingVector y s))
          (L.v (prefixLength s + 1)) =
        ∑ r : Fin (prefixLength s),
          y ⟨r.1, lt_trans r.2 (prefixLength_lt s)⟩ *
            vdot (L.v (r.1 + 1)) (L.v (prefixLength s + 1)) := by
    simp only [ritzVector, Vmat, ofCols_mulVec, vdot, dotProduct,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp [leadingVector, descentPrefix]
    ring
  rw [hritz, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  simp only [prefixLength]



theorem prefix_eigen_expansion (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (y : Vec t) (s : Fin (t - 1)) :
    ∑ r : Fin (prefixLength s),
        L.descentCoeff t ht0 htk y s r •
          L.prefixEigenvector t ht0 htk s r = leadingVector y s := by
  let B := (L.prefixHermitian t ht0 htk s).eigenvectorBasis
  let x : EuclideanSpace ℝ (Fin (prefixLength s)) :=
    WithLp.toLp 2 (leadingVector y s)
  have h := B.sum_repr' x
  have hfun := congrArg (fun z => WithLp.ofLp z) h
  have hinner : ∀ r : Fin (prefixLength s),
      inner ℝ (B r) x = L.descentCoeff t ht0 htk y s r := by
    intro r
    calc
      inner ℝ (B r) x =
          vdot (leadingVector y s) (L.prefixEigenvector t ht0 htk s r) := by
            simpa [B, x, prefixEigenvector, vdot, star_trivial] using
              (EuclideanSpace.inner_toLp_toLp
                (L.prefixEigenvector t ht0 htk s r) (leadingVector y s))
      _ = vdot (L.prefixEigenvector t ht0 htk s r) (leadingVector y s) := by
            exact dotProduct_comm _ _
      _ = L.descentCoeff t ht0 htk y s r := by rfl
  simp_rw [hinner] at hfun
  ext i
  have hi := congrFun hfun i
  simpa [B, x, descentCoeff, prefixEigenvector, vdot,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_trivial] using hi



theorem physical_prefix_eigen_expansion
    (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (y : Vec t) (s : Fin (t - 1)) :
    vdot ((L.descentPrefix t ht0 htk s).ritzVector (leadingVector y s))
        (L.v (prefixLength s + 1)) =
      ∑ r : Fin (prefixLength s),
        L.descentCoeff t ht0 htk y s r * L.descentCorr t ht0 htk s r := by
  rw [← L.prefix_eigen_expansion t ht0 htk y s]
  simp only [ritzVector, Matrix.mulVec_sum, Matrix.mulVec_smul, vdot,
    dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    descentCorr]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring



theorem rho_expansion (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (y : Vec t) :
    vdot y ((L.take t ht0 htk).Rmat *ᵥ y) =
      ∑ s : Fin (t - 1), ∑ r : Fin (prefixLength s),
        L.descentCoeff t ht0 htk y s r *
          L.descentCorr t ht0 htk s r * descentTail y s := by
  rw [L.rho_expansion_physical t ht0 htk y]
  apply Finset.sum_congr rfl
  intro s _
  rw [L.physical_prefix_eigen_expansion t ht0 htk y s, Finset.sum_mul]





lemma leading_vdot_le (t : ℕ) (y : Vec t) (s : Fin (t - 1)) :
    vdot (leadingVector y s) (leadingVector y s) ≤ vdot y y := by
  let emb : Fin (prefixLength s) → Fin t := fun i =>
    ⟨i.1, lt_trans i.2 (prefixLength_lt s)⟩
  change (∑ i : Fin (prefixLength s), y (emb i) * y (emb i)) ≤
    ∑ j : Fin t, y j * y j
  have hinj : Function.Injective emb := by
    intro i j h
    apply Fin.ext
    exact Fin.mk.inj h
  calc
    ∑ i : Fin (prefixLength s), y (emb i) * y (emb i)
        = ∑ j ∈ Finset.univ.image emb, y j * y j := by
          rw [Finset.sum_image]
          exact hinj.injOn
    _ ≤ ∑ j : Fin t, y j * y j := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro j _ _
          exact mul_self_nonneg (y j)


lemma descentTail_sq_sum_le (t : ℕ) (ht0 : 0 < t) (y : Vec t) :
    (∑ s : Fin (t - 1), (descentTail y s) ^ 2) ≤ vdot y y := by
  cases t with
  | zero => omega
  | succ q =>
      simp only [Nat.succ_sub_one]
      rw [vdot, dotProduct, Fin.sum_univ_succ]
      change (∑ s : Fin q, (descentTail y s) ^ 2) ≤
        y 0 * y 0 + ∑ i : Fin q, y i.succ * y i.succ
      have heq :
          (∑ s : Fin q, (descentTail y s) ^ 2) =
            ∑ s : Fin q, y s.succ ^ 2 := by
        apply Finset.sum_congr rfl
        intro s _
        congr 2
      rw [heq]
      have hz : 0 ≤ y (0 : Fin (q + 1)) * y 0 := mul_self_nonneg _
      have hs : 0 ≤ ∑ i : Fin q, y i.succ ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      simp only [pow_two]
      linarith


lemma descentCoeff_sq_sum (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (y : Vec t) (s : Fin (t - 1)) :
    (∑ r : Fin (prefixLength s), (L.descentCoeff t ht0 htk y s r) ^ 2) =
      vdot (leadingVector y s) (leadingVector y s) := by
  let B := (L.prefixHermitian t ht0 htk s).eigenvectorBasis
  let x : EuclideanSpace ℝ (Fin (prefixLength s)) :=
    WithLp.toLp 2 (leadingVector y s)
  have hp := B.sum_sq_inner_right x
  have hinner : ∀ r : Fin (prefixLength s),
      inner ℝ (B r) x = L.descentCoeff t ht0 htk y s r := by
    intro r
    calc
      inner ℝ (B r) x =
          vdot (leadingVector y s) (L.prefixEigenvector t ht0 htk s r) := by
            simpa [B, x, prefixEigenvector, vdot, star_trivial] using
              (EuclideanSpace.inner_toLp_toLp
                (L.prefixEigenvector t ht0 htk s r) (leadingVector y s))
      _ = vdot (L.prefixEigenvector t ht0 htk s r) (leadingVector y s) :=
            dotProduct_comm _ _
      _ = L.descentCoeff t ht0 htk y s r := rfl
  simp_rw [hinner] at hp
  rw [← vnorm_sq]
  simpa [x, vnorm] using hp



lemma descentCoeff_abs_sum_le (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (y : Vec t) (hy : vdot y y = 1) (s : Fin (t - 1)) :
    (∑ r : Fin (prefixLength s), |L.descentCoeff t ht0 htk y s r|) ≤
      Real.sqrt (prefixLength s) := by
  have hsq :
      (∑ r : Fin (prefixLength s), (L.descentCoeff t ht0 htk y s r) ^ 2) ≤ 1 := by
    rw [L.descentCoeff_sq_sum t ht0 htk y s]
    exact (leading_vdot_le t y s).trans_eq hy
  have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun r : Fin (prefixLength s) => |L.descentCoeff t ht0 htk y s r|)
    (fun _r : Fin (prefixLength s) => 1)
  simp only [Finset.sum_const_zero, Finset.card_univ, Fintype.card_fin,
    one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, abs_pow] at hc
  have hsqrtSq :
      Real.sqrt (∑ r : Fin (prefixLength s),
        |L.descentCoeff t ht0 htk y s r| ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    simpa using hsq
  calc
    ∑ r : Fin (prefixLength s), |L.descentCoeff t ht0 htk y s r|
        ≤ Real.sqrt (∑ r : Fin (prefixLength s),
            |L.descentCoeff t ht0 htk y s r| ^ 2) *
          Real.sqrt (prefixLength s) := by simpa using hc
    _ ≤ 1 * Real.sqrt (prefixLength s) :=
      mul_le_mul_of_nonneg_right hsqrtSq (Real.sqrt_nonneg _)
    _ = Real.sqrt (prefixLength s) := one_mul _


private lemma indexSucc_sum_le_half_sq (q : ℕ) :
    (∑ s : Fin q, ((s.1 + 1 : ℕ) : ℝ)) ≤ ((q + 1 : ℕ) : ℝ) ^ 2 / 2 := by
  induction q with
  | zero => norm_num
  | succ q ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
      have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
      norm_num at ih ⊢
      nlinarith [sq_nonneg (q : ℝ)]


lemma prefixLength_sum_le_half_sq (t : ℕ) (ht0 : 0 < t) :
    (∑ s : Fin (t - 1), (prefixLength s : ℝ)) ≤ (t : ℝ) ^ 2 / 2 := by
  cases t with
  | zero => omega
  | succ q =>
      change (∑ s : Fin q, ((s.1 + 1 : ℕ) : ℝ)) ≤
        (((q + 1 : ℕ) : ℝ) ^ 2) / 2
      exact indexSucc_sum_le_half_sq q



theorem descent_aggregate_bound
    (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (y : Vec t) (hy : vdot y y = 1) :
    (∑ s : Fin (t - 1), ∑ r : Fin (prefixLength s),
      ((descentTail y s) ^ 2 +
        |L.descentCoeff t ht0 htk y s r * descentTail y s|))
      ≤ (2 : ℝ) * t := by
  have htail : (∑ s : Fin (t - 1), (descentTail y s) ^ 2) ≤ 1 := by
    exact (descentTail_sq_sum_le t ht0 y).trans_eq hy
  have htR : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  have hfirst :
      (∑ s : Fin (t - 1), ∑ _r : Fin (prefixLength s),
        (descentTail y s) ^ 2) ≤ (t : ℝ) := by
    calc
      (∑ s : Fin (t - 1), ∑ _r : Fin (prefixLength s),
          (descentTail y s) ^ 2)
          = ∑ s : Fin (t - 1),
              (prefixLength s : ℝ) * (descentTail y s) ^ 2 := by simp
      _ ≤ ∑ s : Fin (t - 1),
              (t : ℝ) * (descentTail y s) ^ 2 := by
            apply Finset.sum_le_sum
            intro s _
            exact mul_le_mul_of_nonneg_right
              (by exact_mod_cast (prefixLength_lt s).le) (sq_nonneg _)
      _ = (t : ℝ) * ∑ s : Fin (t - 1), (descentTail y s) ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ (t : ℝ) * 1 := mul_le_mul_of_nonneg_left htail htR
      _ = (t : ℝ) := mul_one _
  have hinner : ∀ s : Fin (t - 1),
      (∑ r : Fin (prefixLength s),
        |L.descentCoeff t ht0 htk y s r * descentTail y s|) ≤
        Real.sqrt (prefixLength s) * |descentTail y s| := by
    intro s
    simp_rw [abs_mul, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right
      (L.descentCoeff_abs_sum_le t ht0 htk y hy s) (abs_nonneg _)
  have hcauchy := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun s : Fin (t - 1) => Real.sqrt (prefixLength s))
    (fun s : Fin (t - 1) => |descentTail y s|)
  simp only [Real.sq_sqrt (Nat.cast_nonneg _), sq_abs] at hcauchy
  have hsumLen := prefixLength_sum_le_half_sq t ht0
  have hsqrtLen :
      Real.sqrt (∑ s : Fin (t - 1), (prefixLength s : ℝ)) ≤
        (3 / 4 : ℝ) * t := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have ht2 : 0 ≤ (t : ℝ) ^ 2 := sq_nonneg _
      nlinarith
  have hsqrtTail :
      Real.sqrt (∑ s : Fin (t - 1), (descentTail y s) ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact htail
  have hsecond :
      (∑ s : Fin (t - 1), ∑ r : Fin (prefixLength s),
        |L.descentCoeff t ht0 htk y s r * descentTail y s|) ≤
        (3 / 4 : ℝ) * t := by
    calc
      (∑ s : Fin (t - 1), ∑ r : Fin (prefixLength s),
          |L.descentCoeff t ht0 htk y s r * descentTail y s|)
          ≤ ∑ s : Fin (t - 1),
              Real.sqrt (prefixLength s) * |descentTail y s| :=
            Finset.sum_le_sum fun s _ => hinner s
      _ ≤ Real.sqrt (∑ s : Fin (t - 1), (prefixLength s : ℝ)) *
          Real.sqrt (∑ s : Fin (t - 1), (descentTail y s) ^ 2) := by
            simpa using hcauchy
      _ ≤ ((3 / 4 : ℝ) * t) * 1 :=
            mul_le_mul hsqrtLen hsqrtTail (Real.sqrt_nonneg _) (by positivity)
      _ = (3 / 4 : ℝ) * t := mul_one _
  simp_rw [Finset.sum_add_distrib]
  linarith



theorem paige_descent
    (t : ℕ) (ht0 : 0 < t) (htk : t ≤ k)
    (y : Vec t) (theta : ℝ) (hy : vdot y y = 1)
    (heig : (L.take t ht0 htk).Tmat *ᵥ y = theta • y)
    (hloss : (3 / 8 : ℝ) <
      |vdot y ((L.take t ht0 htk).Rmat *ᵥ y)|) :
    ∃ s : Fin (t - 1), ∃ r : Fin (prefixLength s),
      |theta - L.prefixEigenvalue t ht0 htk s r| ≤
          8 * t * ((6000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖) ∧
      L.β (prefixLength s) *
          |L.prefixEigenvector t ht0 htk s r
            ⟨prefixLength s - 1, by
              have := prefixLength_pos s
              omega⟩| ≤
          8 * t * ((6000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖) := by
  let E : ℝ := (6000 * (k : ℝ) ^ 3) * L.ε * ‖L.H‖
  let rho : ℝ := vdot y ((L.take t ht0 htk).Rmat *ᵥ y)
  have hE : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity)
        (pow_nonneg (Nat.cast_nonneg k) 3)) L.hε_nonneg)
      (norm_nonneg _)
  have hsel := paige_descent_selection ht0 E rho hE
    (L.descentGap t ht0 htk theta)
    (L.descentEdge t ht0 htk)
    (L.descentCoeff t ht0 htk y)
    (L.descentCorr t ht0 htk)
    (descentTail y)
    (L.descent_coefficient_identity t ht0 htk y theta heig)
    (fun s r => L.leading_paige_product_bound t ht0 htk s r)
    (by
      dsimp [rho]
      exact L.rho_expansion t ht0 htk y)
    (L.descent_aggregate_bound t ht0 htk y hy)
    (by simpa [rho] using hloss)
  obtain ⟨s, r, hgap, hedge⟩ := hsel
  refine ⟨s, r, ?_, ?_⟩
  · simpa [descentGap, E] using hgap
  · have hb : 0 ≤ L.β (prefixLength s) :=
      L.hβ_nonneg _ ((prefixLength_lt s).le.trans htk)
    simpa [descentEdge, E, abs_mul, abs_of_nonneg hb] using hedge

end LanczosRun
end FinitePrecisionLanczos
