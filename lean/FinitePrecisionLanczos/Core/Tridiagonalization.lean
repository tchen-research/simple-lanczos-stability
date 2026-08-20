import FinitePrecisionLanczos.Lanczos.Greenbaum.Correction
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Exact symmetric tridiagonalization with a prescribed first vector

This file formalizes the exact-Lanczos continuation/restart step used in
lem:completion.  The theorem is deliberately stated at the level of an
orthonormal basis: its matrix entries are inner products, so the three-term
structure can be audited directly.
-/

namespace FinitePrecisionLanczos

open scoped InnerProductSpace
open Module Submodule

/-- The upper-triangle half of the usual tridiagonal zero pattern.  For a
symmetric matrix this is equivalent to tridiagonality. -/
def Matrix.UpperTridiagonal {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, i.1 + 1 < j.1 → T i j = 0

/-- Compression of a linear operator to a subspace by orthogonal projection. -/
noncomputable def compressedOperator {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (K : Submodule ℝ E) : K →ₗ[ℝ] K :=
  K.orthogonalProjectionOnto.toLinearMap.comp (A.comp K.subtype)

@[simp]
lemma compressedOperator_apply_coe {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (K : Submodule ℝ E) (x : K) :
    ((compressedOperator A K x : K) : E) = K.starProjection (A x) := by
  rfl

/-- Orthogonal compression preserves symmetry. -/
theorem compressedOperator_isSymmetric {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) (K : Submodule ℝ E) :
    (compressedOperator A K).IsSymmetric := by
  intro x y
  change ⟪K.orthogonalProjectionOnto (A x), y⟫_ℝ =
    ⟪x, K.orthogonalProjectionOnto (A y)⟫_ℝ
  rw [K.inner_orthogonalProjectionOnto_eq_of_mem_left,
    K.inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact hA x y

/-- Matrix entries in an orthonormal basis are the corresponding inner
products. -/
lemma toMatrix_orthonormalBasis_apply {E : Type*} {n : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (b : OrthonormalBasis (Fin n) ℝ E) (i j : Fin n) :
    A.toMatrix b.toBasis b.toBasis i j = ⟪b i, A (b j)⟫_ℝ := by
  calc
    _ = b.repr (A (b j)) i := A.toMatrix_apply ..
    _ = ⟪b i, A (b j)⟫_ℝ := b.repr_apply_apply ..

/-- A finite-dimensional symmetric operator has an orthonormal
tridiagonalizing basis whose first vector is any prescribed unit vector.

This is the machine-checked version of "continue exact Lanczos, restarting in
an invariant orthogonal complement after a breakdown" in lem:completion.
-/
theorem exists_orthonormalBasis_upperTridiagonal_with_first
    (d : ℕ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (hdim : finrank ℝ E = d + 1)
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (q : E) (hq : ‖q‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (d + 1)) ℝ E,
      b 0 = q ∧ Matrix.UpperTridiagonal (A.toMatrix b.toBasis b.toBasis) := by
  classical
  induction d generalizing E with
  | zero =>
      have hq0 : q ≠ 0 := by
        intro h
        simp [h] at hq
      let v : Fin 1 → E := fun _ => q
      have hv : Orthonormal ℝ v := by
        rw [orthonormal_iff_ite]
        intro i j
        have hij : i = j := Subsingleton.elim _ _
        subst j
        simp [v, inner_self_eq_norm_sq_to_K, hq]
      have hv_univ : Orthonormal ℝ (Set.univ.restrict v) := by
        exact hv.comp (fun i : (Set.univ : Set (Fin 1)) => i.1)
          Subtype.val_injective
      obtain ⟨b, hb⟩ :=
        Orthonormal.exists_orthonormalBasis_extension_of_card_eq
          (𝕜 := ℝ) (E := E) (ι := Fin 1) (v := v) (s := Set.univ)
          (by simpa using hdim) hv_univ
      refine ⟨b, ?_, ?_⟩
      · exact hb 0 (Set.mem_univ _)
      · intro i j hij
        omega
  | succ d ih =>
      have hq0 : q ≠ 0 := by
        intro h
        simp [h] at hq
      let K : Submodule ℝ E := ℝ ∙ q
      let P : Submodule ℝ E := Kᗮ
      have hKdim : finrank ℝ K = 1 := by
        simpa [K] using finrank_span_singleton hq0
      have hPdim : finrank ℝ P = d + 1 := by
        have hsum := K.finrank_add_finrank_orthogonal
        rw [hKdim, hdim] at hsum
        change finrank ℝ Kᗮ = d + 1
        omega
      let AP : P →ₗ[ℝ] P := compressedOperator A P
      have hAP : AP.IsSymmetric := compressedOperator_isSymmetric A hA P
      let r : P := P.orthogonalProjectionOnto (A q)
      let q₁ : P := if hr : r = 0 then
          ((stdOrthonormalBasis ℝ P).reindex (finCongr hPdim)) 0
        else (‖r‖⁻¹ : ℝ) • r
      have hq₁ : ‖q₁‖ = 1 := by
        simp only [q₁]
        split_ifs with hr
        · exact ((stdOrthonormalBasis ℝ P).reindex (finCongr hPdim)).norm_eq_one 0
        · exact norm_smul_inv_norm hr
      obtain ⟨bP, hbP0, hbPtri⟩ := ih hPdim AP hAP q₁ hq₁
      let v : Fin (d + 2) → E := fun i =>
        Fin.cases q (fun j => ((bP j : P) : E)) i
      have hv : Orthonormal ℝ v := by
        rw [orthonormal_iff_ite]
        intro i j
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => simp [v, inner_self_eq_norm_sq_to_K, hq]
            | succ j' =>
                have hjmem : ((bP j' : P) : E) ∈ P := (bP j').property
                have hqK : q ∈ K := by simp [K]
                have hne : (0 : Fin (d + 2)) ≠ j'.succ := by
                  intro h
                  have := congrArg Fin.val h
                  simp at this
                simpa [v, hne] using
                  Submodule.inner_right_of_mem_orthogonal hqK hjmem
        | succ i' =>
            cases j using Fin.cases with
            | zero =>
                have himem : ((bP i' : P) : E) ∈ P := (bP i').property
                have hqK : q ∈ K := by simp [K]
                simpa [v] using
                  Submodule.inner_left_of_mem_orthogonal hqK himem
            | succ j' =>
                simpa [v] using orthonormal_iff_ite.mp bP.orthonormal i' j'
      have hv_univ : Orthonormal ℝ (Set.univ.restrict v) := by
        exact hv.comp (fun i : (Set.univ : Set (Fin (d + 2))) => i.1)
          Subtype.val_injective
      obtain ⟨b, hb⟩ :=
        Orthonormal.exists_orthonormalBasis_extension_of_card_eq
          (𝕜 := ℝ) (E := E) (ι := Fin (d + 2)) (v := v) (s := Set.univ)
          (by simpa using hdim) hv_univ
      refine ⟨b, hb 0 (Set.mem_univ _), ?_⟩
      intro i j hij
      have hb_all : ∀ t, b t = v t := fun t => hb t (Set.mem_univ _)
      rw [toMatrix_orthonormalBasis_apply, hb_all i, hb_all j]
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              simp only [Fin.val_zero] at hij
              omega
          | succ j' =>
              by_cases hj0 : j' = 0
              · subst j'
                simp only [Fin.val_zero, Fin.val_succ] at hij
                omega
              · have hjq₁ : ⟪(bP j' : P), q₁⟫_ℝ = 0 := by
                  have horth := orthonormal_iff_ite.mp bP.orthonormal j' 0
                  rw [hbP0] at horth
                  simpa [hj0] using horth
                simp only [v, Fin.cases_zero, Fin.cases_succ]
                have hproj : ⟪((bP j' : P) : E), A q⟫_ℝ =
                    ⟪((bP j' : P) : E), (r : E)⟫_ℝ := by
                  change ⟪((bP j' : P) : E), A q⟫_ℝ =
                    ⟪((bP j' : P) : E),
                      P.orthogonalProjectionOnto (A q)⟫_ℝ
                  symm
                  exact P.inner_orthogonalProjectionOnto_eq_of_mem_left
                    (bP j') (A q)
                have htail : ⟪((bP j' : P) : E), A q⟫_ℝ = 0 := by
                  rw [hproj]
                  by_cases hr : r = 0
                  · simp [hr]
                  · have hrnorm : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
                    have hscaled := hjq₁
                    simp [q₁, hr, inner_smul_right, hrnorm] at hscaled
                    exact hscaled
                calc
                  ⟪q, A ((bP j' : P) : E)⟫_ℝ =
                      ⟪A q, ((bP j' : P) : E)⟫_ℝ :=
                    (hA q (((bP j' : P) : E))).symm
                  _ = ⟪((bP j' : P) : E), A q⟫_ℝ := real_inner_comm _ _
                  _ = 0 := htail
      | succ i' =>
          cases j using Fin.cases with
          | zero =>
              simp only [Fin.val_zero, Fin.val_succ] at hij
              omega
          | succ j' =>
              simp only [v, Fin.cases_succ]
              have hij_tail : i'.1 + 1 < j'.1 := by
                simp only [Fin.val_succ] at hij
                omega
              have hentry := hbPtri i' j' hij_tail
              rw [toMatrix_orthonormalBasis_apply] at hentry
              change ⟪((bP i' : P) : E), A (bP j')⟫_ℝ = 0
              have hproj :
                  ⟪(bP i' : P), AP (bP j')⟫_ℝ =
                    ⟪((bP i' : P) : E), A (bP j')⟫_ℝ := by
                change
                  ⟪bP i',
                    P.orthogonalProjectionOnto (A (bP j'))⟫_ℝ = _
                exact P.inner_orthogonalProjectionOnto_eq_of_mem_left
                  (bP i') (A (bP j'))
              exact hproj ▸ hentry

end FinitePrecisionLanczos
