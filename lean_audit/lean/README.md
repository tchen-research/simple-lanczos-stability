# Lean development

A Lean 4 / Mathlib formalization of the finite-precision Lanczos analysis in
`../body.tex` (compiled as `../finite_precision_lanczos.pdf`). See
`../FORMALIZATION_MAP.md` for the label-by-label correspondence with the paper.

```
lake build          # from this directory
```

Toolchain `leanprover/lean4:v4.32.2`, Mathlib pinned at `v4.32.2` in
`lakefile.toml`. A fresh checkout should run `lake exe cache get` before
`lake build`. (On this machine `.lake/packages` is a symlink to an existing
Mathlib build elsewhere on disk, purely to avoid re-downloading it; that
symlink is gitignored and nothing in the source depends on it.)

## Layout

```
FinitePrecisionLanczos/
  Core/                  general mathematics -- no `LanczosRun` anywhere
    Matrix.lean            Euclidean vectors, spectral-norm matrices
    Commutator.lean        exact commutator and sandwich identities
    Spectral.lean          real symmetric spectral intervals
    Descent.lean           scalar core of the descent argument
    Nilpotent.lean         nilpotent triangular augmentation
    Dilation.lean          exact physical block dilation
    DilationRecurrence.lean  propagating a recurrence through the copies
    DilationBounds.lean    explicit bounds for the dilation
    Tridiagonalization.lean  tridiagonalization with a prescribed first vector
    CompletionBasis.lean   completion of an exact initial Lanczos block
    Completion.lean        matrix form of the completion theorem
    CompletionCorrection.lean  the symmetric backward correction
    Measure/               finite atomic measures and transport distances
  Lanczos/               the analysis of a computed run
    Run.lean               the arithmetic model (paper sec:model)
    Bounds.lean            local error bounds
    Assembly.lean          prefix matrices from the columnwise model
    Paige/                 paper sec:paige
    Greenbaum/             paper sec:greenbaum
```

The split is mechanical and checkable: no file under `Core/` mentions
`LanczosRun`. Those statements are about arbitrary matrices, vectors, and
measures, so they apply at every prefix length without re-instantiation --
the design the paper's own discussion of formalization calls for. `Lanczos/`
instantiates them at the objects assembled from a run.

`Lanczos/Paige/Statements.lean` and `Lanczos/Greenbaum/Statements.lean`
collect the paper-facing theorems; the proofs behind them stay split into
small lemmas in the neighbouring files.

## What is checked

Everything is `sorry`-free and uses no axioms beyond Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`), verified with `#print axioms`
on the top-level results below.

| Declaration | Paper | Content |
|---|---|---|
| `LanczosRun` | `sec:model` | the run as a structure: computed data plus the defining identities |
| `local_errors` | `thm:local-errors` | the local error bounds, with explicit constants |
| `gram_commutator_conclusion` | `lem:gram-commutator` | the Gram commutator identity and its bound |
| `paige_bound` | `thm:paige` | Paige's loss-of-orthogonality bound, with explicit constant `6000 k³` |
| `containment`, `stabilized` | `thm:containment`, `thm:stabilized` | Ritz value containment and stabilization |
| `normalized_local_errors` | `lem:normalized-errors` | local errors for the normalized quantities |
| `normalized_gram_commutator` | `lem:normalized-commutator` | the normalized commutator bound |
| `nilpotent_isometry` | `lem:isometry` | `K` nilpotent, `‖K‖ ≤ 1`, the three identities |
| `physical_dilation` | `lem:dilation` | the dilated basis, boundary vector, and residual bound |
| `exists_greenbaumModel` | `thm:greenbaum` | existence of the backward model |
| `eigenvalue_localization` | `thm:greenbaum` (iii) | every model eigenvalue near `spec(A)` |
| `starting_moment` | `thm:greenbaum` (ii) | starting weights preserved exactly |
| `exact_lanczos_returns_Tmat` | `thm:greenbaum` | exact Lanczos on the model returns the computed `T_k` |
| `starting_cluster_mass` | -- | cluster-mass agreement in `W₁`, beyond the paper |

Unlike an earlier stage of this development, the inequalities are now proved:
norms, the local bounds, the commutator bounds, and the dilation residual all
carry explicit constants. Where the paper writes `\lesssim_k`, the Lean
statements name the polynomial in `k`.

## Modelling caveat

There is no theorem saying that running Algorithm 1 produces a `LanczosRun`.
The structure is a family of arbitrary objects satisfying the defining
identities, so "the analysis applies to the algorithm" remains a modelling
claim, exactly as the paper says it must. What the structure does guarantee is
that every result uses only those identities and the stated interface bounds.

The index convention of the paper is used: real steps are `1, 2, 3, …`, index
`0` carries the phantoms `v 0 = 0` and `β 0 = 0`, and structure fields are
stated at `j + 1`, so truncated subtraction on `ℕ` never appears.
