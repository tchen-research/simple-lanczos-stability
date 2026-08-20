-- Core: general linear algebra
import FinitePrecisionLanczos.Core.Matrix
import FinitePrecisionLanczos.Core.Commutator
import FinitePrecisionLanczos.Core.Spectral
import FinitePrecisionLanczos.Core.Descent

-- Core: the nilpotent dilation
import FinitePrecisionLanczos.Core.Nilpotent
import FinitePrecisionLanczos.Core.Dilation
import FinitePrecisionLanczos.Core.DilationRecurrence
import FinitePrecisionLanczos.Core.DilationBounds

-- Core: symmetric completion
import FinitePrecisionLanczos.Core.Tridiagonalization
import FinitePrecisionLanczos.Core.CompletionBasis
import FinitePrecisionLanczos.Core.Completion
import FinitePrecisionLanczos.Core.CompletionCorrection

-- Core: finite atomic measures and transport
import FinitePrecisionLanczos.Core.Measure.FiniteAtomic
import FinitePrecisionLanczos.Core.Measure.SpectralMass
import FinitePrecisionLanczos.Core.Measure.Transport
import FinitePrecisionLanczos.Core.Measure.Wasserstein
import FinitePrecisionLanczos.Core.Measure.Cutoff
import FinitePrecisionLanczos.Core.Measure.SpectralWassersteinCore
import FinitePrecisionLanczos.Core.Measure.SpectralWasserstein
import FinitePrecisionLanczos.Core.Measure.ClusterGeometry

-- Lanczos: the arithmetic model (paper sec:model)
import FinitePrecisionLanczos.Lanczos.Run
import FinitePrecisionLanczos.Lanczos.Bounds
import FinitePrecisionLanczos.Lanczos.Assembly

-- Lanczos: Paige's theory (paper sec:paige)
import FinitePrecisionLanczos.Lanczos.Paige.Commutator
import FinitePrecisionLanczos.Lanczos.Paige.Loss
import FinitePrecisionLanczos.Lanczos.Paige.LossBounds
import FinitePrecisionLanczos.Lanczos.Paige.Ritz
import FinitePrecisionLanczos.Lanczos.Paige.Prefix
import FinitePrecisionLanczos.Lanczos.Paige.Descent
import FinitePrecisionLanczos.Lanczos.Paige.Containment
import FinitePrecisionLanczos.Lanczos.Paige.Stabilized
import FinitePrecisionLanczos.Lanczos.Paige.Statements

-- Lanczos: Greenbaum's theory (paper sec:greenbaum)
import FinitePrecisionLanczos.Lanczos.Greenbaum.Interface
import FinitePrecisionLanczos.Lanczos.Greenbaum.Normalization
import FinitePrecisionLanczos.Lanczos.Greenbaum.NormalizedRecurrence
import FinitePrecisionLanczos.Lanczos.Greenbaum.NormalizedCommutator
import FinitePrecisionLanczos.Lanczos.Greenbaum.Dilation
import FinitePrecisionLanczos.Lanczos.Greenbaum.Correction
import FinitePrecisionLanczos.Lanczos.Greenbaum.Completion
import FinitePrecisionLanczos.Lanczos.Greenbaum.Model
import FinitePrecisionLanczos.Lanczos.Greenbaum.Reproduction
import FinitePrecisionLanczos.Lanczos.Greenbaum.Statements

-- Lanczos: spectral consequences of the backward model
import FinitePrecisionLanczos.Lanczos.Greenbaum.Spectral
import FinitePrecisionLanczos.Lanczos.Greenbaum.Measure
import FinitePrecisionLanczos.Lanczos.Greenbaum.SpectralMass
import FinitePrecisionLanczos.Lanczos.Greenbaum.Wasserstein
import FinitePrecisionLanczos.Lanczos.Greenbaum.Cluster

/-!
# Finite-precision Lanczos: machine-checked companion

This is the root of the Lean development accompanying
`finite_precision_lanczos.tex`.  Declaration docstrings cite LaTeX labels in
that file.  The formal statements use explicit constants; the paper may hide
their polynomial dependence on the iteration count with `\lesssim_k`.

## Layout

The development is split into two layers.

* `Core/` is general mathematics: matrix and vector norms, the nilpotent
  dilation, symmetric completion and tridiagonalization, and finite atomic
  measures with their transport distances.  Nothing in `Core/` mentions
  `LanczosRun`; every statement is about arbitrary matrices, vectors, or
  measures, and so applies at any prefix length without re-instantiation.

* `Lanczos/` is the analysis of a computed run.  `Lanczos/Run.lean` fixes the
  arithmetic model, and `Lanczos/Paige/` and `Lanczos/Greenbaum/` follow
  `sec:paige` and `sec:greenbaum` of the paper.  The `Statements.lean` file in
  each of those directories collects the paper-facing theorems.

See `../FORMALIZATION_MAP.md` for the label-by-label correspondence with the
paper.
-/
