/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import TauCeti.Analysis.SpecialFunctions.Erf
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma
public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta

/-!
# DLMF Chapters 6–8 results already in Mathlib or TauCeti

The `dlmf_upstream` commands below are checked source pointers, deliberately not duplicate
local theorems. The pinned Mathlib has neither named exponential/error/Fresnel functions nor
complex incomplete Gamma/Beta continuations. Its `Complex.partialGamma` does cover the
positive-real-argument lower incomplete Gamma integral. The real error/inverse
functions imported by the project belong to TauCeti, including the declaration
`Real.erfInv` in TauCeti's source; the namespace alone does not identify ownership.

The alternative notations of §8.1 are aliases for existing functions: Prym's
P_z(a), Q_z(a) mean `DLMF.Confluent.lowerIncGamma a z`, `upperIncGamma a z`;
(a,z)! and [a,z]! shift that parameter to a+1. B(a,b,x), I(a,b,x) name the
incomplete Beta functions, and Luke's generalized trigonometric parameter is
1-a. These notational aliases do not introduce new mathematical functions.

The former equation 8.18.13 was retired in DLMF 1.1.8; its slot now points to
5.11.3. The scaled Gamma definition is recorded in `gammaScaled`, and the
project's proved logarithmic Stirling expansion is in DLMF/Gamma/Asymptotics.lean.
-/

/- DLMF 7.2.1–7.2.2 for real arguments: TauCeti's real error functions. The project's
complex `erf`, `erfc` carry their own `@[dlmf]` tags. -/
dlmf_upstream 7.2.E1 TauCeti.Real.erf
  "special case: real argument x; erf x = (2/√π) ∫₀ˣ exp(-t²) dt"
dlmf_upstream 7.2.E2 TauCeti.Real.erfc_def
  "partial: second equality erfc x = 1 - erf x, real argument only"

/- DLMF 7.7.6 with b = c = x = 0: the Gaussian integral over the half-line. Its full-line
counterpart is the limit x → -∞ of the same formula. -/
dlmf_upstream 7.7.E6 integral_gaussian_complex_Ioi
  "special case: b = c = x = 0, Re a > 0; ∫₀^∞ exp(-a t²) dt = (π/a)^{1/2}/2, principal power"
dlmf_upstream 7.7.E6 integral_gaussian_complex
  "special case: b = c = 0 and the limit x → -∞ (integral over ℝ), Re a > 0"

/- DLMF 8.2.1 on real X ≥ 0: `Complex.partialGamma` is the defining interval integral.
The local complex-argument continuation and its bridge remain separate obligations. -/
dlmf_upstream 8.2.E1 Complex.partialGamma
  "special case: real upper limit X ≥ 0 and Re a > 0; the interval integral is Bochner-totalized \
  (0 when it diverges, Re a ≤ 0)"
dlmf_upstream 8.2.E1 TauCeti.lowerIncompleteGamma_eq_integral
  "special case: real a > 0 and real x ≥ 0"
dlmf_upstream 8.2.E4 TauCeti.regularizedGamma_eq_div
  "partial: P(a,x) = γ(a,x)/Γ(a) for real a, x; TauCeti's γ and P are 0 for a ≤ 0 or x ≤ 0, \
  Q is not defined"

/- DLMF 8.8.1 on real X ≥ 0 and Re a > 0. The existing project recurrence extends its
parameter and argument coverage. -/
dlmf_upstream 8.8.E1 Complex.partialGamma_add_one
  "special case: real z = X ≥ 0 and Re a > 0"

/- DLMF 8.17.2 for real parameters: TauCeti's regularized incomplete Beta function. -/
dlmf_upstream 8.17.E2 TauCeti.regularizedIncompleteBeta_def_of_mem_Icc
  "special case: real a, b > 0 and 0 ≤ x ≤ 1, with B(a,b) = ProbabilityTheory.beta a b"

/- DLMF 8.17.3: the complete Beta integral `Complex.betaIntegral` as a Gamma quotient.
No local proof of the displayed Gamma quotient is introduced. -/
dlmf_upstream 8.17.E3 Complex.betaIntegral_eq_Gamma_mul_div
  "special case: Re a > 0, Re b > 0, with B(a,b) the Euler integral Complex.betaIntegral"
