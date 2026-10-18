import FinitePrecisionLanczos.Core.Matrix


namespace FinitePrecisionLanczos

open Matrix
open scoped Matrix.Norms.L2Operator

section Frobenius

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

def frobSq (X : Matrix ι κ ℝ) : ℝ := ∑ a, ∑ b, X a b ^ 2

noncomputable def frobNorm (X : Matrix ι κ ℝ) : ℝ := Real.sqrt (frobSq X)

lemma frobSq_nonneg (X : Matrix ι κ ℝ) : 0 ≤ frobSq X := by
  unfold frobSq; positivity

/-- The Euclidean operator norm is bounded by the Frobenius norm. -/
theorem opNorm_le_frobNorm [DecidableEq κ] (M : Matrix ι κ ℝ) :
    ‖M‖ ≤ frobNorm M := by
  rw [← norm_indexedMatCLM]
  refine (indexedMatCLM M).opNorm_le_bound (Real.sqrt_nonneg _) fun x => ?_
  have hsq : ‖indexedMatCLM M x‖ ^ 2 ≤ frobSq M * ‖x‖ ^ 2 := by
    rw [indexedMatCLM_apply, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, WithLp.toLp_ofLp]
    calc
      ∑ i, ((M *ᵥ WithLp.ofLp x) i) ^ 2 ≤
          ∑ i, (∑ j, M i j ^ 2) * (∑ j, (WithLp.ofLp x j) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = frobSq M * ‖x‖ ^ 2 := by
        rw [← Finset.sum_mul]
        simp [frobSq, EuclideanSpace.norm_sq_eq, sq_abs]
  have hf : 0 ≤ frobNorm M := Real.sqrt_nonneg _
  have hf2 : frobNorm M ^ 2 = frobSq M := Real.sq_sqrt (frobSq_nonneg M)
  have hr : 0 ≤ frobNorm M * ‖x‖ := mul_nonneg hf (norm_nonneg _)
  nlinarith [norm_nonneg (indexedMatCLM M x)]

lemma frobSq_transpose (X : Matrix ι κ ℝ) : frobSq Xᵀ = frobSq X := by
  unfold frobSq
  rw [Finset.sum_comm]
  rfl

lemma frobSq_neg (X : Matrix ι κ ℝ) : frobSq (-X) = frobSq X := by
  simp [frobSq]

lemma frobNorm_neg (X : Matrix ι κ ℝ) : frobNorm (-X) = frobNorm X := by
  rw [frobNorm, frobNorm, frobSq_neg]

lemma frobSq_eq_trace (X : Matrix ι κ ℝ) : frobSq X = trace (Xᵀ * X) := by
  unfold frobSq
  rw [Finset.sum_comm]
  simp [trace, Matrix.mul_apply, sq]

lemma frobSq_eq_sum_col (X : Matrix ι κ ℝ) :
    frobSq X = ∑ b, coordNorm (fun a => X a b) ^ 2 := by
  unfold frobSq
  rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun b => ?_
  rw [coordNorm_sq]
  simp [dotProduct, sq]

lemma frobSq_split [DecidableEq κ] (X : Matrix ι κ ℝ) (P : Matrix κ κ ℝ)
    (hPt : Pᵀ = P) (hPP : P * P = P) :
    frobSq X = frobSq (X * P) + frobSq (X * (1 - P)) := by
  have hQt : (1 - P)ᵀ = 1 - P := by rw [Matrix.transpose_sub, Matrix.transpose_one, hPt]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hPP]
    abel
  rw [frobSq_eq_trace, frobSq_eq_trace, frobSq_eq_trace, Matrix.transpose_mul,
    Matrix.transpose_mul, hPt, hQt]
  have h1 : trace (P * Xᵀ * (X * P)) = trace (Xᵀ * X * P) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hPP, Matrix.mul_assoc]
    exact Matrix.trace_mul_comm _ _
  have h2 : trace ((1 - P) * Xᵀ * (X * (1 - P))) = trace (Xᵀ * X * (1 - P)) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hQQ, Matrix.mul_assoc]
    exact Matrix.trace_mul_comm _ _
  rw [h1, h2, ← Matrix.trace_add, ← Matrix.mul_add]
  simp

lemma frobSq_mul_transpose [DecidableEq μ] (Y : Matrix ι μ ℝ) (V : Matrix κ μ ℝ) (hV : Vᵀ * V = 1) :
    frobSq (Y * Vᵀ) = frobSq Y := by
  rw [frobSq_eq_trace, frobSq_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hV,
    Matrix.mul_one]

lemma frobSq_mul_le [DecidableEq κ] [DecidableEq μ] (X : Matrix ι κ ℝ) (V : Matrix κ μ ℝ)
    (hV : Vᵀ * V = 1) :
    frobSq (X * V) ≤ Fintype.card μ * ‖X‖ ^ 2 := by
  classical
  rw [frobSq_eq_sum_col]
  have hcol : ∀ j : μ, coordNorm (fun b => V b j) = 1 := by
    intro j
    have hsq : coordNorm (fun b => V b j) ^ 2 = 1 := by
      rw [coordNorm_sq]
      have := congrFun (congrFun hV j) j
      simpa [Matrix.mul_apply, dotProduct] using this
    nlinarith [coordNorm_nonneg (fun b => V b j)]
  calc
    ∑ j, coordNorm (fun a => (X * V) a j) ^ 2
        = ∑ j : μ, coordNorm (X *ᵥ fun b => V b j) ^ 2 := by
          refine Fintype.sum_congr _ _ fun j => ?_
          congr 2
    _ ≤ ∑ _j : μ, ‖X‖ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h := coordNorm_mulVec_le X (fun b => V b j)
          rw [hcol j, mul_one] at h
          exact pow_le_pow_left₀ (coordNorm_nonneg _) h 2
    _ = Fintype.card μ * ‖X‖ ^ 2 := by simp

theorem frobSq_le_of_compression [DecidableEq κ] {k : ℕ} (D : Matrix κ κ ℝ)
    (V : Matrix κ (Fin k) ℝ) (hD : Dᵀ = D) (hV : Vᵀ * V = 1)
    (hcomp : (1 - V * Vᵀ) * D * (1 - V * Vᵀ) = 0) :
    frobSq D ≤ 2 * k * ‖D‖ ^ 2 := by
  set P : Matrix κ κ ℝ := V * Vᵀ with hPdef
  have hPt : Pᵀ = P := by rw [hPdef, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hPP : P * P = P := by
    rw [hPdef, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul]
  have hDP : frobSq (D * P) ≤ k * ‖D‖ ^ 2 := by
    rw [hPdef, ← Matrix.mul_assoc, frobSq_mul_transpose _ _ hV]
    simpa using frobSq_mul_le D V hV
  have hDQ : D * (1 - P) = P * D * (1 - P) := by
    have h : D * (1 - P) = P * D * (1 - P) + (1 - P) * D * (1 - P) := by
      rw [← Matrix.add_mul, ← Matrix.add_mul]
      simp
    rw [h, hcomp, add_zero]
  have hPDQ : frobSq (P * D * (1 - P)) ≤ frobSq (D * P) := by
    have hsplit := frobSq_split (P * D) P hPt hPP
    have htr : frobSq (P * D) = frobSq (D * P) := by
      rw [← frobSq_transpose, Matrix.transpose_mul, hD, hPt]
    have hnn := frobSq_nonneg (P * D * P)
    linarith
  have hsplit := frobSq_split D P hPt hPP
  rw [hDQ] at hsplit
  linarith

theorem frobNorm_le_of_compression [DecidableEq κ] {k : ℕ} (D : Matrix κ κ ℝ)
    (V : Matrix κ (Fin k) ℝ) (hD : Dᵀ = D) (hV : Vᵀ * V = 1)
    (hcomp : (1 - V * Vᵀ) * D * (1 - V * Vᵀ) = 0) :
    frobNorm D ≤ Real.sqrt (2 * k) * ‖D‖ := by
  have h := frobSq_le_of_compression D V hD hV hcomp
  rw [frobNorm, ← Real.sqrt_sq (norm_nonneg D), ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (by linarith)

end Frobenius

end FinitePrecisionLanczos
