# Lean development

A Lean 4 / Mathlib formalization of the finite-precision Lanczos analysis in
[body.tex](../body.tex). See the [proof correspondence map](../FORMALIZATION_MAP.md)
for named results, intermediate proof steps, assumptions, and proof-route differences.

<https://github.com/tchen-research/simple-lanczos-stability>

```
lake build          # from this directory
```

Toolchain `leanprover/lean4:v4.32.2`, Mathlib pinned at `v4.32.2` in
`lakefile.toml`. A fresh checkout should run `lake exe cache get` before
`lake build`. (On this machine `.lake/packages` is a symlink to an existing
Mathlib build elsewhere on disk, purely to avoid re-downloading it; that
symlink is gitignored and nothing in the source depends on it.)

## Closer correspondence with the proof

`beta_recurrence_paper` now proves the printed `(1 + 10ε)β + 2‖H‖`
recurrence. `coefficients_paper` gives the separate sharp coefficient bounds;
`coefficient_multipliers` checks both scalar inequalities on `[0, 1/20]`.
The column and block-stack estimates retain `√k` and `√(k+1)` before
relaxation to the existing polynomial envelopes.

The spectral-measure proof now uses Mathlib's actual matrix `cfc`, the full
Frobenius Lipschitz theorem, `rank(Δ) ≤ 2k`, and the general symmetric
rank-to-Frobenius inequality. The localization theorem also has an explicit
existential eigenvalue form. The nonzero condition on the divided Ritz
residual and the corrected definition of `Δ` appear in both paper and code.

The [updated PDF](../audit_report/alignment_report.pdf) reports these changes.
The older statement audit is retained for the original source snapshot.

## Layout

```
FinitePrecisionLanczos/
  Core/                  general mathematics -- no `LanczosRun` anywhere
    Matrix.lean            Euclidean vectors, spectral-norm matrices, Schur test,
                           ‖X‖ ≤ 1 for orthonormal columns
    Frobenius.lean         ‖X‖ ≤ ‖X‖_F; ‖D‖_F ≤ √(2k)‖D‖ if (I − VVᵀ)D(I − VVᵀ) = 0
    SpectralFrobenius.lean rank counts nonzero eigenvalues; ‖A‖_F ≤ √rank(A) ‖A‖
    Commutator.lean        exact commutator and sandwich identities
    GramCommutator.lean    engine for lem:gram-commutator
                           (eq:gram-commutator-full, eq:generic-commutator)
    Underline.lean         Saad's T̲_k = [T_k; β_k e_kᵀ]; (k+1)-column block
                           algebra (W_k, w_{k+1}, J, JN = [N; 0ᵀ], leading
                           blocks, ‖leadBlock X‖ ≤ ‖X‖)
    SaadGramCommutator.lean  lem:gram-commutator in the paper's form
    Spectral.lean          real symmetric spectral intervals
    BlockSpectral.lean     residual and Rayleigh bounds for I_p ⊗ A
    Nilpotent.lean         nilpotent triangular augmentation, eq:CGC-identity
    Dilation.lean          exact physical block dilation (k+1 copies of R^n),
                           one-telescope orthonormality, eq:Kkp-power,
                           ‖K‖ ≤ 1, ‖C‖ ≤ 2
    DilationRecurrence.lean  rank-one boundary terms, I ⊗ A, the exchange
                           residuals D_r, block errors E_r
    DilationBounds.lean    ‖D_r‖ ≤ r‖L‖, block and stacked error bounds
    DilationSaad.lean      the block computation T̲_kR_k − R_{k+1}T̲_k = JM_k,
                           eq:L-commutator, lem:exchange (powers), and the
                           dilated recurrence ÂV̂_k = V̂_{k+1}T̲_k + Ê (exact algebra)
    BackwardCorrection.lean  Ã = Â − ÊV̂ᵀ − V̂Êᵀ + V̂(V̂ᵀÂV̂ − T)V̂ᵀ:
                           symmetry, eq:delta_as_projector, ‖Δ‖ ≤ 2‖Ê‖, ÃV̂_k = V̂_{k+1}T̲_k
    ExactLanczos.lean      the exact Lanczos process and its identification
                           with an orthonormal exact three-term recurrence
    Measure/               finite atomic spectral measures and W₁;
      FunctionalCalculus.lean  actual cfc, spectral integration, and Frobenius Lipschitz bound
  Lanczos/               the analysis of a computed run
    Run.lean               the arithmetic model (paper sec:model)
    Bounds.lean            local error bounds and lem:coefficients (sec:local)
    Assembly.lean          prefix matrices V_k, T_k, F_k, size of T_k
    Ritz.lean              V_{k+1}, T̲_k, eq:governing (A V_k = V_{k+1}T̲_k + F_k),
                           eq:ritz-residual-identity/bound (sec:loss)
    ComputedCommutator.lean  eq:gram-split (R_k), M_k of eq:M-def,
                           cor:gram-commutator
    LossOfOrthogonality.lean  thm:paige and the dichotomy after it (sec:loss)
    Normalized/            normalized Lanczos vectors (sec:normalized)
      Normalization.lean     d_j, v̄_j (incl. v̄_{k+1}), V̄_k, V̄_{k+1}, eq:normalized-gram-k
      Recurrence.lean        eq:normalized-quantities, eq:normalized-interface
      LocalErrors.lean       lem:normalized-errors
      Commutator.lean        M̄_k of eq:normalized-M-def, cor:normalized-commutator
    Greenbaum/             the backward model and its consequences (sec:backward)
      Dilation.lean          eq:normalized-gram (R̄_{k+1}), eq:CKsy, eq:dilation-def,
                             proofs of lem:dilation, lem:exchange,
                             lem:dilated-recurrence (instances)
      Statements.lean        lem:dilation, lem:exchange, lem:dilated-recurrence
                             as printed (physical_dilation, exchange_rule,
                             dilated_recurrence)
      Correction.lean        Ã, Δ, ṽ and the steps of the proof of thm:greenbaum
      Backward.lean          thm:greenbaum (greenbaum_backward_model)
      Corollaries.lean       thm:stabilized, thm:containment (sec:ritz-consequences)
      Spectral.lean          optional: eigenvalues of Ã near spec(A)
      Measure.lean           optional: ṽᵀÂ^mṽ = v̄_1ᵀA^mv̄_1
      SpectralMass.lean      optional: spectral measure of (Â, ṽ) = that of (A, v̄_1)
      Wasserstein.lean       rem:wasserstein: W₁(μ_{A,v̄_1}, μ_{Ã,ṽ}) ≤ ‖Δ‖_F ≤ √(2k)‖Δ‖
```

The split is mechanical and checkable: no file under `Core/` mentions
`LanczosRun`. Those statements are about arbitrary matrices, vectors, and
measures, so they apply at every prefix length without re-instantiation --
the design the paper's own discussion of formalization calls for. `Lanczos/`
instantiates them at the objects assembled from a run.

The import graph follows the paper's dependency figure.  Notation follows
the paper's subscripts: `V_{k+1} = [V_k, v_{k+1}]` (`Vsucc`), Saad's
`T̲_k = [T_k; β_k e_kᵀ] ∈ ℝ^{(k+1)×k}` (`underlineTmat`), and
`eq:governing` reads `A V_k = V_{k+1} T̲_k + F_k` (`governing`).  The Gram
commutator `lem:gram-commutator` is proved once, for arbitrary
`W_{k+1} = [W_k, w_{k+1}]` with `A W_k = W_{k+1} T̲_k + Z` and
`N_k := T_kY_k − Y_kT_k − β_k(W_kᵀw_{k+1})e_kᵀ` (`Core/SaadGramCommutator.lean`),
and instantiated twice: for the computed vectors (`cor:gram-commutator`,
`ComputedCommutator.lean`, `M_k := T_kR_k − R_kT_k − β_k(V_kᵀv_{k+1})e_kᵀ`),
which feeds `LossOfOrthogonality.lean`, and for the normalized vectors
(`cor:normalized-commutator`, `Normalized/Commutator.lean`,
`M̄_k := T_kR̄_k − R̄_kT_k − β_k(V̄_kᵀv̄_{k+1})e_kᵀ`), which feeds the dilation
in `Greenbaum/Dilation.lean`.  There, as in the proof of `lem:exchange`, the
block form `R̄_{k+1} = [[R̄_k, V̄_kᵀv̄_{k+1}], [0ᵀ, 0]]` of `eq:normalized-gram`
turns the definition of `M̄_k` into `T̲_kR̄_k − R̄_{k+1}T̲_k = JM̄_k`
(`normalizedCommutator_padRow`).  The normalized vectors use the computed
coefficients throughout: `A V̄_k = V̄_{k+1} T̲_k + F̄_k` with the computed
`T̲_k` (there is no separate normalized boundary coefficient).  Neither
`thm:paige` nor the backward model uses the other, and `paige_bound` uses no
normalized-vector declaration.

The dilation is built from `C_{k+1} = (I + R̄_{k+1})⁻¹` and
`K_{k+1} = I − C_{k+1}` (whose leading blocks are `C_k`, `K_k`):
`V̂_{k+1} = col(V̄_{k+1} C_{k+1} K_{k+1}^r)_{r=0}^{k} = [V̂_k, v̂_{k+1}]`
(`greenbaumVhat`, `greenbaumX`, `greenbaumVNext`), with `k + 1` stacked
copies of `R^n`, so the backward model lives in dimension `N = n(k+1)`
(`Fin (k + 1) × Fin n` in Lean).  `lem:dilation` (`physical_dilation`):
`V̂_{k+1}ᵀV̂_{k+1} = I` is one telescoping sum ending at `K_{k+1}^{k+1} = 0`
(`eq:Kkp-power`, `eq:CGC-identity`), and `V̂_{k+1}e_1 = col(v̄_1, 0, …, 0)`.
`lem:exchange` (`exchange_rule`): `‖K_k‖ ≤ 1`, `‖C_k‖ ≤ 2`, `‖L_k‖ ≲ ε‖A‖`
for `L_k = C_kM̄_kC_k`, and `T̲_kK_k^r − K_{k+1}^rT̲_k = JD_r` with
`D_0 = 0`, `D_{r+1} = D_rK_k + K_k^rL_k`, `‖D_r‖ ≤ r‖L_k‖`.
`lem:dilated-recurrence` (`dilated_recurrence`): `ÂV̂_k = V̂_{k+1}T̲_k + Ê`
with blocks `E_r = F̄_kC_kK_k^r + V̄_k(D_r − D_{r+1})`.  `thm:greenbaum`
(`greenbaum_backward_model`): `Ã = Â − ÊV̂_kᵀ − V̂_kÊᵀ + V̂_k(V̂_kᵀÂV̂_k − T_k)V̂_kᵀ`
is symmetric, `‖Â − Ã‖ ≲ ε‖A‖`, `ÃV̂_k = V̂_{k+1}T̲_k`, and `k` steps of the
exact Lanczos process (`Core/ExactLanczos.lean`) applied to
`(Ã, ṽ = col(v̄_1, 0, …, 0))` return exactly the computed `T_k` and `β_k`,
with Lanczos vectors the columns of `V̂_{k+1}`.  `Greenbaum/Corollaries.lean`
deduces `thm:stabilized` and `thm:containment` from it with `x̂ = V̂_ky`.

## What is checked

The post-alignment audit checks every public declaration in the project namespace
and its transitive proof dependencies. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted; a source scan also checks for proof placeholders.
Reproduction commands and evidence are linked from the correspondence map.

| Declaration | Paper | Content |
|---|---|---|
| `LanczosRun` | `sec:model` | the run as a structure: computed data plus the defining identities |
| `local_errors` | `thm:local-errors` | the local error bounds, with explicit constants |
| `coefficients_paper` | `lem:coefficients` | the printed bounds `2‖H‖`, `5j‖H‖`, `6j‖H‖`, `7j‖H‖`, `4j‖H‖`; `coefficients` retains the `100j‖H‖` interface as a corollary |
| `SaadGramRecurrence.gram_commutator` | `lem:gram-commutator` | for `A W_k = W_{k+1}T̲_k + Z` and `N_k := T_kY_k − Y_kT_k − β_k(W_kᵀw_{k+1})e_kᵀ`: `N_k` upper triangular, `‖N_k‖ ≤ 2k(max_{i≤k}\|π_i\| + max‖w_l‖‖Z‖ + max β_i\|γ_{i+1} − γ_i\|)`, `π_i = β_iw_iᵀw_{i+1}` for all `i ≤ k`; proof steps `N_eq`, `N_skew`, `N_upper`, `N_norm_bound` |
| `governing` | `eq:governing` | `A V_k = V_{k+1} T̲_k + F_k` |
| `computed_gram_commutator` | `cor:gram-commutator` | `M_k := T_kR_k − R_kT_k − β_k(V_kᵀv_{k+1})e_kᵀ` (`computedCommutator`, `eq:M-def`) upper triangular, `‖M_k‖ ≤ 3000 k³ ε‖H‖` |
| `ritz_residual_identity`, `ritz_residual_bound` | `eq:ritz-residual-identity`, `eq:ritz-residual-bound` | the Ritz residual |
| `paige_bound` | `thm:paige` | Paige's loss-of-orthogonality bound, directly from the computed Gram commutator `M_k` (`cor:gram-commutator`), constant `3000 k³` |
| `normalized_governing_succ` | `eq:normalized-interface` | `A V̄_k = V̄_{k+1} T̲_k + F̄_k`, columns `f̄_j` of `eq:normalized-quantities` |
| `normalized_local_errors` | `lem:normalized-errors` | for `1 ≤ j ≤ k`: `‖f̄_j‖ ≤ 1500 k ε‖H‖`, `\|p̄_j\| ≤ 4800 k ε‖H‖` |
| `normalized_gram_split` | leading block of `eq:normalized-gram` | `V̄_kᵀV̄_k = I + R̄_kᵀ + R̄_k` |
| `normalized_gram_commutator` | `cor:normalized-commutator` | `M̄_k := T_kR̄_k − R̄_kT_k − β_k(V̄_kᵀv̄_{k+1})e_kᵀ` (`normalizedCommutator`, `eq:normalized-M-def`) upper triangular, `‖M̄_k‖ ≤ 9600 k³ ε‖H‖` |
| `normalized_gram_split_succ`, `normalizedRsucc_block` | `eq:normalized-gram` | `Ḡ_{k+1} = V̄_{k+1}ᵀV̄_{k+1} = I + R̄_{k+1}ᵀ + R̄_{k+1}`, `R̄_{k+1} = [[R̄_k, V̄_kᵀv̄_{k+1}], [0ᵀ, 0]]` |
| `greenbaum_CK_blocks` | `eq:CKsy` | `C_k`, `K_k` are the leading blocks of `C_{k+1}`, `K_{k+1}`; `K_{k+1} = R̄_{k+1}C_{k+1}` |
| `physical_dilation` | `lem:dilation` | `V̂_{k+1}ᵀV̂_{k+1} = I` (one telescoping), `V̂_{k+1}e_1 = col(v̄_1, 0, …, 0)`; proof steps `greenbaum_Kkp_power` (`eq:Kkp-power`), `greenbaum_isometry_identity` (`eq:CGC-identity`) |
| `exchange_rule` | `lem:exchange` | `‖K_k‖ ≤ 1`, `‖C_k‖ ≤ 2`, `‖L_k‖ ≤ 38400 k³ ε‖H‖`, `∀ r, ∃ D, T̲_kK_k^r − K_{k+1}^rT̲_k = JD ∧ ‖D‖ ≤ r‖L_k‖`; proof steps `normalizedCommutator_padRow` (`T̲_kR̄_k − R̄_{k+1}T̲_k = JM̄_k`, from the block form of `R̄_{k+1}`) and `greenbaumL_commutator` (`eq:L-commutator`) |
| `dilated_recurrence` | `lem:dilated-recurrence` | `ÂV̂_k = V̂_{k+1}T̲_k + Ê`, `‖Ê‖ ≤ 240000 k⁶ ε‖H‖`; blocks `E_r = F̄_kC_kK_k^r + V̄_k(D_r − D_{r+1})`, `‖E_r‖ ≤ 120000 k⁵ ε‖H‖` (`block_recurrence`) |
| `greenbaum_backward_model` | `thm:greenbaum` | `Ã` symmetric, `‖Â − Ã‖ ≤ 480000 k⁶ ε‖H‖`, `ÃV̂_k = V̂_{k+1}T̲_k`, `V̂_{k+1}ᵀV̂_{k+1} = I`, `V̂_ke_1 = ṽ`, `exactLanczosT Ã ṽ k = T_k`, `exactLanczosBeta Ã ṽ k = β_k`, no breakdown before step `k`, exact Lanczos vectors = columns of `V̂_{k+1}` |
| `greenbaumDelta_projector`, `greenbaumDelta_norm` | `eq:delta_as_projector` | `Δ = −ÊV̂_kᵀ − V̂_kÊᵀ(I − V̂_kV̂_kᵀ)`, `‖Δ‖ ≤ 2‖Ê‖` |
| `greenbaum_localization` | `thm:stabilized` | `(Ã − θI)x̂ = β_k(e_kᵀy)v̂_{k+1}`, so `dist(θ, spec H) ≤ β_k\|e_kᵀy\| + ‖Δ‖ ≤ β_k\|e_kᵀy\| + 480000 k⁶ ε‖H‖` |
| `greenbaum_containment` | `thm:containment` | every Ritz value within `480000 k⁶ ε‖H‖` of `[λ_min, λ_max]` |
| `greenbaumTildeA_eigenvalue_localization` | -- | every eigenvalue of `Ã` within `‖Δ‖` of `spec(A)`, optional extension |
| `starting_spectralMass` | -- | spectral measure of `(Â, ṽ)` equals that of `(A, v̄_1)`, optional extension |
| `starting_wasserstein` | `rem:wasserstein` | `W₁(μ_{A,v̄_1}, μ_{Ã,ṽ}) ≤ ‖Δ‖_F ≤ √(2k)‖Δ‖` |

Unlike an earlier stage of this development, the inequalities are now proved:
norms, the local bounds, the commutator bounds, and the dilation residual all
carry explicit constants. Where the paper writes `\lesssim_k`, the Lean
statements name the polynomial in `k`.

## Archived Paige route

An earlier version of the paper proved `thm:paige` from a separate unnormalized
Gram commutator lemma (then also labelled `lem:gram-commutator`, but a
different statement) and deduced localization and containment
through Paige's descent argument.  Its formalization (`gram_commutator`,
`upper_commutator`, `gram_commutator_conclusion`, the original
`paige_identity`/`paige_bound` with constant `6000 k³`, `defect_expansion`,
`paige_descent`, and the Paige-route `stabilized`/`containment`) now lives in
`../old/lean_paige_route/`, under its original relative paths
(`FinitePrecisionLanczos/Lanczos/Paige/`, `FinitePrecisionLanczos/Core/Descent.lean`,
`FinitePrecisionLanczos/Lanczos/Greenbaum/Interface.lean`, and the
transport-based `FinitePrecisionLanczos/Lanczos/Greenbaum/NormalizedCommutator.lean`).
It is not imported by the root and is not built.  It is a snapshot of the
pre-reorganization tree: the definitions it shared with the current route
(`lastIndex`, `rawBoundary`, `ritzVector`, the Schur test,
...) now live in `Lanczos/Ritz.lean`, `Lanczos/Assembly.lean`, and
`Core/Matrix.lean`, so rebuilding it would require adjusting its imports.

## Archived completion route

The previous version of the paper stated `thm:greenbaum` through an
orthogonal completion `Ṽ` and a tridiagonal `T̃` (`lem:completion`), and
proved `lem:dilated-recurrence` with `E_0 = F̄_kC_k − V̄_kL_k`.  That
formalization (`GreenbaumModel`, `exists_greenbaumModel`,
`greenbaum_exact_completion`, `ExactLanczos` on `(T̃, e_1)`, the
tridiagonalization with prescribed first vector, and the `T̃`-based
corollaries and spectral extensions) is archived, unbuilt, as a snapshot of
the pre-sync files in `../old/lean_completion_route/`, under original
relative paths.

## Modelling caveat

There is no theorem saying that running Algorithm 1 produces a `LanczosRun`.
The structure is a family of arbitrary objects satisfying the defining
identities, so "the analysis applies to the algorithm" remains a modelling
claim, exactly as the paper says it must. What the structure does guarantee is
that every result uses only those identities and the stated interface bounds.

The index convention of the paper is used: real steps are `1, 2, 3, …`, index
`0` carries the phantoms `v 0 = 0` and `β 0 = 0`, and structure fields are
stated at `j + 1`, so truncated subtraction on `ℕ` never appears.
