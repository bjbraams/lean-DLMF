/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# DLMF Chapter 5 results already in Mathlib 4.35.0-rc2

The `dlmf_upstream` commands below are checked pointers to Mathlib (and TauCeti)
declarations, deliberately not duplicate local theorems; Mathlib's cross-reference
attribute cannot modify documentation on imported declarations. Mathlib's `Complex.Gamma`
is `0` at the poles `0, -1, -2, …` and `Complex.digamma = logDeriv Gamma` is therefore `0`
there as well.
-/

-- Euler's integral.
dlmf_upstream 5.2.E1 Complex.Gamma_eq_integral
  "exact: Re z > 0; Mathlib's GammaIntegral s is ∫₀^∞ e^{-t} t^{s-1} dt"
dlmf_upstream 5.2.E1 Real.Gamma_eq_integral "special case: real z > 0"

-- Digamma as logarithmic derivative; the project's real form is `Real.digamma`.
dlmf_upstream 5.2.E2 Complex.digamma
  "different convention: ψ = logDeriv Γ, totalized to 0 at z = 0, -1, -2, …"

-- Euler–Mascheroni constant.
dlmf_upstream 5.2.E3 Real.tendsto_harmonic_sub_log
  "partial: the limit H_n - ln n → γ, with γ = Real.eulerMascheroniConstant; the decimal \
  value is not formalized (numerical, out of scope)"

-- `(a)_n = Γ(a+n)/Γ(a)` at regular `a`.
dlmf_upstream 5.2.E5 Complex.Gamma_add_nat_div_Gamma_eq
  "exact: a ≠ 0, -1, -2, …; (a)_n is (ascPochhammer ℂ n).eval a"

-- `Γ(1) = 1` and `Γ(n+1) = n!`.
dlmf_upstream 5.4.E1 Complex.Gamma_one "partial: first equality Γ(1) = 1"
dlmf_upstream 5.4.E1 Complex.Gamma_nat_eq_factorial "partial: second equality n! = Γ(n+1)"
dlmf_upstream 5.4.E1 Real.Gamma_one "partial: first equality, real Gamma"
dlmf_upstream 5.4.E1 Real.Gamma_nat_eq_factorial "partial: second equality, real Gamma"

-- `Γ(1/2) = √π`.
dlmf_upstream 5.4.E6 Complex.Gamma_one_half_eq
  "partial: Γ(1/2) = π^{1/2}; the decimal value is not formalized (numerical, out of scope)"
dlmf_upstream 5.4.E6 Real.Gamma_one_half_eq
  "partial: Γ(1/2) = √π for the real Gamma; the decimal value is out of scope"

-- `ψ(1) = -γ`; project: `Real.digamma_one`.
dlmf_upstream 5.4.E12 Complex.digamma_one
  "partial: ψ(1) = -γ; the decimal value is not formalized (numerical, out of scope)"

-- `ψ(1/2) = -γ - 2 ln 2`; project: `digamma_one_div_two`.
dlmf_upstream 5.4.E13 Complex.digamma_one_half
  "partial: ψ(1/2) = -γ - 2 ln 2; the decimal value is not formalized (numerical, out of scope)"

-- Recurrence.
dlmf_upstream 5.5.E1 Complex.Gamma_add_one
  "exact: z ≠ 0; at the other poles both sides are Mathlib's totalized value 0"
dlmf_upstream 5.5.E1 Real.Gamma_add_one "special case: real z ≠ 0"

-- Digamma recurrence; project: `Real.digamma_add_one`.
dlmf_upstream 5.5.E2 Complex.digamma_apply_add_one "exact: z ≠ 0, -1, -2, …"

-- Euler reflection.
dlmf_upstream 5.5.E3 Complex.Gamma_mul_Gamma_one_sub
  "exact: stated for all z; at the integers both sides are Mathlib's totalized value 0"
dlmf_upstream 5.5.E3 Real.Gamma_mul_Gamma_one_sub "special case: real z"

-- Digamma reflection.
dlmf_upstream 5.5.E4 Complex.digamma_one_sub
  "exact: z ∉ ℤ, in the rearranged form ψ(1-z) = ψ(z) + π cot(πz)"

-- Legendre duplication.
dlmf_upstream 5.5.E5 Complex.Gamma_mul_Gamma_add_half
  "exact: rearranged as Γ(z)Γ(z+1/2) = Γ(2z) 2^{1-2z} √π; stated for all z, both sides \
  are Mathlib's totalized value 0 when 2z ∈ -ℕ"
dlmf_upstream 5.5.E5 Real.Gamma_mul_Gamma_add_half "special case: real z, rearranged form"

-- Digamma duplication; project real rearrangement: `digamma_add_digamma_add_half`.
dlmf_upstream 5.5.E8 Complex.digamma_two_mul "exact: 2z ≠ 0, -1, -2, …"

-- Gauss's product/limit.
dlmf_upstream 5.8.E1 Complex.GammaSeq_tendsto_Gamma
  "exact: GammaSeq z k = k^z k!/(z(z+1)⋯(z+k)); stated for all z, both sides totalized to 0 \
  at the poles"
dlmf_upstream 5.8.E1 Real.GammaSeq_tendsto_Gamma "special case: real z"

-- Beta integral and Gamma quotient; project: `selberg_integral_one`.
dlmf_upstream 5.12.E1 Complex.betaIntegral
  "partial: the first equality, B(a,b) as the Euler integral; the interval integral is \
  Bochner-totalized for Re a ≤ 0 or Re b ≤ 0"
dlmf_upstream 5.12.E1 Complex.betaIntegral_eq_Gamma_mul_div
  "exact: Re a > 0, Re b > 0 (both equalities, with Complex.betaIntegral as the integral)"
dlmf_upstream 5.12.E1 Complex.Gamma_mul_Gamma_eq_betaIntegral
  "partial: second equality in the form Γ(a)Γ(b) = Γ(a+b) B(a,b), Re a > 0, Re b > 0"
dlmf_upstream 5.12.E1 TauCeti.integral_rpow_mul_one_sub_rpow
  "special case: real a, b > 0, with B = ProbabilityTheory.beta, the Gamma quotient"

/-! ### Further Chapter 5 statements in Mathlib -/

-- §5.2(i): analytic properties of `Γ` and `1/Γ`.
dlmf_upstream 5.2.i Complex.Gamma_ne_zero
  "partial: Γ has no zeros, z ∉ {0, -1, -2, …} (Mathlib's totalized value at the poles is 0)"
dlmf_upstream 5.2.i Complex.differentiable_one_div_Gamma "partial: 1/Γ is entire"

-- §5.5(iv): the Bohr–Mollerup theorem.
dlmf_upstream 5.5.iv Real.eq_Gamma_of_log_convex
  "exact: a positive f on (0,∞) with f(x+1) = x f(x), f(1) = 1 and ln f convex equals Γ there"
