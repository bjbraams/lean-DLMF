/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Hypergeometric.EulerHalfLine
public import DLMF.Hypergeometric.Boundary
public import DLMF.Hypergeometric.AnalyticProperties
public import DLMF.Hypergeometric.Asymptotics
public import DLMF.Hypergeometric.SeriesProperties
public import DLMF.Hypergeometric.ConnectionFormulas
public import DLMF.Hypergeometric.LogConnectionsRecipGamma
public import DLMF.Hypergeometric.Contiguous
public import DLMF.Hypergeometric.ContinuedFractions
public import DLMF.Hypergeometric.Continuation
public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.Hypergeometric.Derivatives
public import DLMF.Hypergeometric.DiffEq
public import DLMF.Hypergeometric.Elementary
public import DLMF.Hypergeometric.EulerIntegral
public import DLMF.Hypergeometric.FurtherTransformations
public import DLMF.Hypergeometric.Identities
public import DLMF.Hypergeometric.IntegralRepresentations
public import DLMF.Hypergeometric.Kummer
public import DLMF.Hypergeometric.Riemann
public import DLMF.Hypergeometric.Solutions
public import DLMF.Hypergeometric.Transformations
public import DLMF.Hypergeometric.BarnesAux
public import DLMF.Hypergeometric.Generalized
public import DLMF.Hypergeometric.LoopIntegral
public import DLMF.Hypergeometric.Saalschutz
public import DLMF.Hypergeometric.AppellF4
public import DLMF.Hypergeometric.FiniteConvolution
public import DLMF.Hypergeometric.GeneralizedCalculus
public import DLMF.Hypergeometric.GeneralizedContinuity
public import DLMF.Hypergeometric.GeneralizedIntegral
public import DLMF.Hypergeometric.Clausen
public import DLMF.Hypergeometric.SpecialCases
public import DLMF.Hypergeometric.ParameterHolomorphy
public import DLMF.Hypergeometric.MathlibCoverage
public import DLMF.Hypergeometric.SpecialValueTools
public import DLMF.Hypergeometric.CubicTools

/-!
# The hypergeometric function (AAR Chapters 2 and 3; DLMF Chapter 15)

Mathlib already supplies the Gaussian series `₂F₁` (`ordinaryHypergeometric`), its radius of
convergence, the regularized generalized series, and the binomial series
`(1+x)^a`. The imported modules record AAR Chapter 2–3 identities and suitable statements
from DLMF §§15.2, 15.4–15.8, and 15.10–15.12 that are absent from Mathlib.
Each statement taken from the DLMF records its equation number in a `@[dlmf]`
attribute. Many newly acquired statements are admitted and remain proof obligations.

From Duverney, *An Introduction to Hypergeometric Functions*, Chapters 3–4 (all proved):
Pfaff–Saalschütz (`Saalschutz`); the derivative, contiguous relation, uniqueness of power-series
solutions and Euler–Pochhammer integral of the general `ₚFq` (`GeneralizedCalculus`,
`GeneralizedIntegral`); Clausen's formula with Euler's `arcsin²` series and
`π² = 18 ∑ 1/(n² C(2n,n))` (`Clausen`); and `Si` as a `₁F₂` (`SpecialCases`).
-/
