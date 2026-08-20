import FinitePrecisionLanczos.Core.Measure.Transport

/-!
# One-Wasserstein distance for finite atomic masses

This is a finite-sum version of one-Wasserstein distance.  It avoids
measure-theoretic overhead because every spectral measure in the paper has
finite support.
-/

namespace FinitePrecisionLanczos

/-- Integral of a scalar function against a finite atomic mass. -/
noncomputable def atomicIntegral (mu : AtomicMass) (f : ℝ → ℝ) : ℝ :=
  mu.sum fun x w => w * f x

@[simp] lemma atomicIntegral_zero (f : ℝ → ℝ) : atomicIntegral 0 f = 0 := by
  simp [atomicIntegral]

@[simp] lemma atomicIntegral_add (mu nu : AtomicMass) (f : ℝ → ℝ) :
    atomicIntegral (mu + nu) f = atomicIntegral mu f + atomicIntegral nu f := by
  classical
  unfold atomicIntegral
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

@[simp] lemma atomicIntegral_single (x w : ℝ) (f : ℝ → ℝ) :
    atomicIntegral (Finsupp.single x w) f = w * f x := by
  classical
  simp [atomicIntegral]

/-- The scalar one-Lipschitz condition used below. -/
def OneLipschitz (f : ℝ → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ |x - y|

/-- Kantorovich--Rubinstein definition of `W₁` for finite atomic masses. -/
noncomputable def atomicWasserstein (mu nu : AtomicMass) : ℝ :=
  sSup {r : ℝ | ∃ f : ℝ → ℝ,
    OneLipschitz f ∧
      r = |atomicIntegral mu f - atomicIntegral nu f|}

/-- To bound finite-atomic `W₁`, it suffices to bound every one-Lipschitz
test function. -/
theorem atomicWasserstein_le (mu nu : AtomicMass) (C : ℝ)
    (hC : ∀ f : ℝ → ℝ, OneLipschitz f →
      |atomicIntegral mu f - atomicIntegral nu f| ≤ C) :
    atomicWasserstein mu nu ≤ C := by
  unfold atomicWasserstein
  apply csSup_le
  · refine ⟨0, fun _ => 0, ?_, ?_⟩
    · simp [OneLipschitz]
    · simp [atomicIntegral]
  · intro r hr
    obtain ⟨f, hf, rfl⟩ := hr
    exact hC f hf

end FinitePrecisionLanczos
