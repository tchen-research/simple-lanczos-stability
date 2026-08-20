import FinitePrecisionLanczos.Lanczos.Paige.Descent
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Real symmetric spectral interval

This file contains the self-contained Mathlib bridge used by
`thm:containment` and `thm:stabilized`: definitions of the two spectral
endpoints and the multiplied-out Rayleigh inequalities.
-/

namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

/-- Smallest eigenvalue of a nonempty real symmetric matrix.  The fallback
value is used only outside the theorem hypotheses. -/
noncomputable def spectralMin (H : Mat n n) : ℝ :=
  letI := Classical.propDecidable (H.IsHermitian ∧ 0 < n)
  if h : H.IsHermitian ∧ 0 < n then
    Finset.univ.inf' (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp h.2))
      h.1.eigenvalues
  else 0

/-- Largest eigenvalue of a nonempty real symmetric matrix. -/
noncomputable def spectralMax (H : Mat n n) : ℝ :=
  letI := Classical.propDecidable (H.IsHermitian ∧ 0 < n)
  if h : H.IsHermitian ∧ 0 < n then
    Finset.univ.sup' (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp h.2))
      h.1.eigenvalues
  else 0

/-- Distance from a real number to the eigenvalue set of a nonempty real
symmetric matrix.  This is the finite-dimensional meaning of
`dist(theta, spec(H))` used in `thm:stabilized`. -/
noncomputable def spectralDistance (H : Mat n n) (theta : ℝ) : ℝ :=
  letI := Classical.propDecidable (H.IsHermitian ∧ 0 < n)
  if h : H.IsHermitian ∧ 0 < n then
    Finset.univ.inf' (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp h.2))
      (fun i => |theta - h.1.eigenvalues i|)
  else 0

lemma spectralMin_le (hn : 0 < n) {H : Mat n n} (hH : H.IsHermitian) (i : Fin n) :
    spectralMin H ≤ hH.eigenvalues i := by
  unfold spectralMin
  rw [dif_pos ⟨hH, hn⟩]
  exact Finset.inf'_le _ (Finset.mem_univ i)

lemma le_spectralMax (hn : 0 < n) {H : Mat n n} (hH : H.IsHermitian) (i : Fin n) :
    hH.eigenvalues i ≤ spectralMax H := by
  unfold spectralMax
  rw [dif_pos ⟨hH, hn⟩]
  exact Finset.le_sup' _ (Finset.mem_univ i)

lemma spectralDistance_nonneg (hn : 0 < n) {H : Mat n n} (hH : H.IsHermitian)
    (theta : ℝ) : 0 ≤ spectralDistance H theta := by
  unfold spectralDistance
  rw [dif_pos ⟨hH, hn⟩]
  apply Finset.le_inf' (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
  intro i _
  exact abs_nonneg _

lemma spectralDistance_le (hn : 0 < n) {H : Mat n n} (hH : H.IsHermitian)
    (theta : ℝ) (i : Fin n) :
    spectralDistance H theta ≤ |theta - hH.eigenvalues i| := by
  unfold spectralDistance
  rw [dif_pos ⟨hH, hn⟩]
  exact Finset.inf'_le _ (Finset.mem_univ i)

/-- The finite spectral distance is attained by one enumerated eigenvalue. -/
lemma exists_eigenvalue_abs_eq_spectralDistance (hn : 0 < n)
    {H : Mat n n} (hH : H.IsHermitian) (theta : ℝ) :
    ∃ i : Fin n, |theta - hH.eigenvalues i| = spectralDistance H theta := by
  let S : Finset (Fin n) := Finset.univ
  have hS : S.Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  let f : Fin n → ℝ := fun i => |theta - hH.eigenvalues i|
  have hmem : S.inf' hS f ∈ Set.range f := by
    apply Finset.inf'_mem (Set.range f)
    · intro a ha b hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      by_cases hij : f i ≤ f j
      · exact ⟨i, (inf_eq_left.mpr hij).symm⟩
      · exact ⟨j, (inf_eq_right.mpr (le_of_not_ge hij)).symm⟩
    · intro i _hi
      exact ⟨i, rfl⟩
  obtain ⟨i, hi⟩ := hmem
  refine ⟨i, ?_⟩
  unfold spectralDistance
  rw [dif_pos ⟨hH, hn⟩]
  simpa [S, f] using hi

/-- Moving the scalar argument changes distance to the finite spectrum by at
most the scalar displacement. -/
lemma spectralDistance_triangle (hn : 0 < n) {H : Mat n n}
    (hH : H.IsHermitian) (theta theta' : ℝ) :
    spectralDistance H theta ≤ |theta - theta'| + spectralDistance H theta' := by
  let S : Finset (Fin n) := Finset.univ
  have hS : S.Nonempty := Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  let f : Fin n → ℝ := fun i => |theta' - hH.eigenvalues i|
  have hmem : S.inf' hS f ∈ Set.range f := by
    apply Finset.inf'_mem (Set.range f)
    · intro a ha b hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      by_cases hij : f i ≤ f j
      · exact ⟨i, (inf_eq_left.mpr hij).symm⟩
      · exact ⟨j, (inf_eq_right.mpr (le_of_not_ge hij)).symm⟩
    · intro i _hi
      exact ⟨i, rfl⟩
  obtain ⟨i, hi⟩ := hmem
  have hnearest : spectralDistance H theta' = |theta' - hH.eigenvalues i| := by
    unfold spectralDistance
    rw [dif_pos ⟨hH, hn⟩]
    simpa [S, f] using hi.symm
  calc
    spectralDistance H theta ≤ |theta - hH.eigenvalues i| :=
      spectralDistance_le hn hH theta i
    _ ≤ |theta - theta'| + |theta' - hH.eigenvalues i| := by
      calc
        |theta - hH.eigenvalues i| =
            |(theta - theta') + (theta' - hH.eigenvalues i)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    _ = |theta - theta'| + spectralDistance H theta' := by rw [hnearest]

lemma isHermitian_spectral_decomposition {H : Mat n n} (hH : H.IsHermitian) :
    H = (hH.eigenvectorUnitary : Mat n n) * Matrix.diagonal hH.eigenvalues *
      star (hH.eigenvectorUnitary : Mat n n) := by
  conv_lhs => rw [hH.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp]

lemma posSemidef_smul_one_sub {H : Mat n n} (hH : H.IsHermitian) {c : ℝ}
    (hc : ∀ i, hH.eigenvalues i ≤ c) : (c • (1 : Mat n n) - H).PosSemidef := by
  have hdecomp := isHermitian_spectral_decomposition hH
  let U : Mat n n := (hH.eigenvectorUnitary : Mat n n)
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hdiag : (Matrix.diagonal (fun i => c - hH.eigenvalues i) : Mat n n)
      = c • (1 : Mat n n) - Matrix.diagonal hH.eigenvalues := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hkey : c • (1 : Mat n n) - H =
      U * Matrix.diagonal (fun i => c - hH.eigenvalues i) * star U := by
    rw [hdiag, mul_sub, sub_mul, Matrix.mul_smul, mul_one, Matrix.smul_mul, hUU,
      ← hdecomp]
  rw [hkey, Matrix.star_eq_conjTranspose]
  exact (Matrix.posSemidef_diagonal_iff.mpr
    fun i => sub_nonneg.mpr (hc i)).mul_mul_conjTranspose_same U

lemma posSemidef_sub_smul_one {H : Mat n n} (hH : H.IsHermitian) {c : ℝ}
    (hc : ∀ i, c ≤ hH.eigenvalues i) : (H - c • (1 : Mat n n)).PosSemidef := by
  have hdecomp := isHermitian_spectral_decomposition hH
  let U : Mat n n := (hH.eigenvectorUnitary : Mat n n)
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hdiag : (Matrix.diagonal (fun i => hH.eigenvalues i - c) : Mat n n)
      = Matrix.diagonal hH.eigenvalues - c • (1 : Mat n n) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hkey : H - c • (1 : Mat n n) =
      U * Matrix.diagonal (fun i => hH.eigenvalues i - c) * star U := by
    rw [hdiag, mul_sub, sub_mul, Matrix.mul_smul, mul_one, Matrix.smul_mul, hUU,
      ← hdecomp]
  rw [hkey, Matrix.star_eq_conjTranspose]
  exact (Matrix.posSemidef_diagonal_iff.mpr
    fun i => sub_nonneg.mpr (hc i)).mul_mul_conjTranspose_same U

/-- Upper multiplied-out Rayleigh bound. -/
theorem vdot_mulVec_le_spectralMax (hn : 0 < n) {H : Mat n n} (hH : Hᵀ = H)
    (z : Vec n) : vdot z (H *ᵥ z) ≤ spectralMax H * vdot z z := by
  have hherm := isHermitian_of_transpose_eq hH
  have hpsd := posSemidef_smul_one_sub hherm (fun i => le_spectralMax hn hherm i)
  have h0 := hpsd.dotProduct_mulVec_nonneg z
  rw [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at h0
  change 0 ≤ spectralMax H * vdot z z - vdot z (H *ᵥ z) at h0
  linarith

/-- Lower multiplied-out Rayleigh bound. -/
theorem spectralMin_mul_vdot_le (hn : 0 < n) {H : Mat n n} (hH : Hᵀ = H)
    (z : Vec n) : spectralMin H * vdot z z ≤ vdot z (H *ᵥ z) := by
  have hherm := isHermitian_of_transpose_eq hH
  have hpsd := posSemidef_sub_smul_one hherm (fun i => spectralMin_le hn hherm i)
  have h0 := hpsd.dotProduct_mulVec_nonneg z
  rw [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at h0
  change 0 ≤ vdot z (H *ᵥ z) - spectralMin H * vdot z z at h0
  linarith

/-- Multiplication by the adjoint eigenvector matrix preserves the Euclidean
vector norm.  This is the explicit Parseval step in the residual argument. -/
lemma vnorm_star_eigenvectorUnitary_mulVec (hn : 0 < n) {H : Mat n n}
    (hH : H.IsHermitian) (z : Vec n) :
    vnorm (star (hH.eigenvectorUnitary : Mat n n) *ᵥ z) = vnorm z := by
  let Ugroup := hH.eigenvectorUnitary
  let U : Mat n n := (Ugroup : Mat n n)
  let C : Mat n n := star U
  have hCtranspose : C = Uᵀ := by
    simp [C, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  have hUC : U * C = 1 := by
    dsimp [U, C, Ugroup]
    exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hUC' : U * Uᵀ = 1 := by simpa [hCtranspose] using hUC
  have hCtC : Cᵀ * C = 1 := by rw [hCtranspose, Matrix.transpose_transpose, hUC']
  have hdot : vdot (C *ᵥ z) (C *ᵥ z) = vdot z z := by
    have hadjoint : vdot (C *ᵥ z) (C *ᵥ z) =
        vdot z ((Cᵀ * C) *ᵥ z) := by
      calc
        vdot (C *ᵥ z) (C *ᵥ z) = vdot z (Cᵀ *ᵥ (C *ᵥ z)) := by
          exact (Matrix.dotProduct_transpose_mulVec C z (C *ᵥ z)).symm
        _ = vdot z ((Cᵀ * C) *ᵥ z) := by rw [Matrix.mulVec_mulVec]
    rw [hadjoint, hCtC, Matrix.one_mulVec]
  have hsquares : vnorm (C *ᵥ z) ^ 2 = vnorm z ^ 2 := by
    rw [vnorm_sq, vnorm_sq]
    exact hdot
  have hleft := vnorm_nonneg (C *ᵥ z)
  have hright := vnorm_nonneg z
  simpa [C, U, Ugroup] using (sq_eq_sq₀ hleft hright).mp hsquares

/-- Residual characterization of distance to the spectrum for a real
symmetric matrix, in multiplied-out form. -/
theorem spectralDistance_mul_vnorm_le_residual (hn : 0 < n)
    {H : Mat n n} (hHtranspose : Hᵀ = H) (theta : ℝ) (z : Vec n) :
    spectralDistance H theta * vnorm z ≤ vnorm (H *ᵥ z - theta • z) := by
  let hH := isHermitian_of_transpose_eq hHtranspose
  let U : Mat n n := (hH.eigenvectorUnitary : Mat n n)
  let C : Mat n n := star U
  let c : Vec n := C *ᵥ z
  let residual : Vec n := H *ᵥ z - theta • z
  let transformed : Vec n := C *ᵥ residual
  have hCU : C * U = 1 := by
    dsimp [C, U, hH]
    exact Unitary.coe_star_mul_self
      (isHermitian_of_transpose_eq hHtranspose).eigenvectorUnitary
  have hdecomp : H = U * Matrix.diagonal hH.eigenvalues * C := by
    simpa [U, C, hH] using isHermitian_spectral_decomposition hH
  have hCH : C * H = Matrix.diagonal hH.eigenvalues * C := by
    calc
      C * H = C * (U * Matrix.diagonal hH.eigenvalues * C) :=
        congrArg (fun M => C * M) hdecomp
      C * (U * Matrix.diagonal hH.eigenvalues * C) =
          (C * U) * Matrix.diagonal hH.eigenvalues * C := by noncomm_ring
      _ = Matrix.diagonal hH.eigenvalues * C := by rw [hCU, one_mul]
  have hcoordinate : ∀ i : Fin n,
      transformed i = (hH.eigenvalues i - theta) * c i := by
    intro i
    dsimp [transformed, residual, c]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    change (C *ᵥ (H *ᵥ z)) i - theta * (C *ᵥ z) i = _
    rw [Matrix.mulVec_mulVec, hCH, ← Matrix.mulVec_mulVec]
    simp [Matrix.mulVec]
    ring
  have hcNorm : vnorm c = vnorm z := by
    simpa [c, C, U, hH] using
      vnorm_star_eigenvectorUnitary_mulVec hn hH z
  have htNorm : vnorm transformed = vnorm residual := by
    simpa [transformed, C, U, hH] using
      vnorm_star_eigenvectorUnitary_mulVec hn hH residual
  let d := spectralDistance H theta
  have hd : 0 ≤ d := by
    exact spectralDistance_nonneg hn hH theta
  have hterm : ∀ i : Fin n,
      d ^ 2 * c i ^ 2 ≤ transformed i ^ 2 := by
    intro i
    have hgap := spectralDistance_le hn hH theta i
    have hgapSq : d ^ 2 ≤ |theta - hH.eigenvalues i| ^ 2 :=
      pow_le_pow_left₀ hd hgap 2
    rw [hcoordinate]
    have hcSq : 0 ≤ c i ^ 2 := sq_nonneg _
    calc
      d ^ 2 * c i ^ 2 ≤ |theta - hH.eigenvalues i| ^ 2 * c i ^ 2 :=
        mul_le_mul_of_nonneg_right hgapSq hcSq
      _ = ((hH.eigenvalues i - theta) * c i) ^ 2 := by
        rw [sq_abs]
        ring
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hterm i
  have hsq : d ^ 2 * vnorm c ^ 2 ≤ vnorm transformed ^ 2 := by
    calc
      d ^ 2 * vnorm c ^ 2 = ∑ i : Fin n, d ^ 2 * c i ^ 2 := by
        rw [vnorm_sq]
        simp only [vdot, dotProduct, pow_two, Finset.mul_sum]
      _ ≤ ∑ i : Fin n, transformed i ^ 2 := hsum
      _ = vnorm transformed ^ 2 := by
        rw [vnorm_sq]
        simp only [vdot, dotProduct, pow_two]
  rw [hcNorm, htNorm] at hsq
  have hz0 := vnorm_nonneg z
  have hr0 := vnorm_nonneg residual
  have hdv : 0 ≤ d * vnorm z := mul_nonneg hd hz0
  nlinarith [sq_nonneg (d * vnorm z - vnorm residual)]

end FinitePrecisionLanczos
