/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic.CrossRefAttribute
public import DLMFMathlib.Analysis.ODE.Singularities
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic

/-!
# Heun functions: definitions (DLMF Chapter 31)

This file holds the definitions of DLMF Chapter 31 (namespace `DLMF.Heun`).

* `IsLinearODE2On p r w s`: `w'' + p w' + r w = 0` on `s`, with genuine differentiability, the
  shape of every second-order equation of the chapter. Heun's equation (31.2.1) is
  `IsHeunSolOn a q α β γ δ ε w s`; the exponent parameter `ε` is kept explicit and Fuchs's
  relation `α + β + 1 = γ + δ + ε` is a hypothesis wherever DLMF needs it. `heunODECoeff` is the
  same equation in the form of `Complex.linearODEValue` (DLMFMathlib, singularity
  classification).
* The coefficients `P_j, Q_j, R_j` of the three-term recurrence (31.3.4), the Maclaurin
  coefficients `c_j` of the local solution (`heunLocalCoeff`, 31.3.2–31.3.3) and the local Heun
  function `heunLocal a q α β γ δ z = ∑ c_j z^j` (31.3.1). In `heunLocal` the parameter
  `ε = α + β + 1 - γ - δ` (`heunEps`). The series converges for `|z| < min(1, |a|)`
  (`heunLocalRadius`); outside that disk, and when `aγ = 0` or `γ ∈ {-1, -2, …}` (where a
  denominator `R_j` vanishes), the `tsum` and the totalized divisions are junk values.
* Heun functions (§31.4): `IsHeunFunctionOn`, the eigenvalue predicate `IsHeunEigenvalue01`, the
  continuation `heunFunction01` (by choice) and the continued fraction `heunCFApprox` (31.4.2).
* Heun polynomials (§31.5): the tridiagonal matrix `heunPolyMatrix` (31.5.1) and the
  truncated series `heunPoly` (31.5.2).
* Contour integrals with continuously continued branches: `localBranchCpow`, the Pochhammer
  double loop `pochhammerLoop`, and `continuedPathIntegral` (integral along a path of the analytic
  continuation of a germ, via TauCeti's `IsAnalyticContinuationAlong`); path-multiplicative
  solutions (§31.6).
* Heun's operator `heunOperator` (31.10.4) and the weights of §31.10.
* The confluent forms (§31.12), the rank of an irregular singularity, the general Fuchsian
  equation (§31.14) and Stieltjes/Van Vleck polynomials (§31.15).
-/

@[expose] public section

open Complex Filter Set Polynomial
open scoped Topology Real

noncomputable section

namespace DLMF.Heun

/-! ### Second-order linear equations -/

/-- `w'' + p w' + r w = 0` on `s`: `w` is differentiable at every point of `s` and its derivative
has derivative `-(p w' + r w)` there. Genuine differentiability is required, so totalized
derivatives cannot make a nonsolution satisfy the equation. -/
structure IsLinearODE2On (p r : ℂ → ℂ) (w : ℂ → ℂ) (s : Set ℂ) : Prop where
  differentiableAt : ∀ z ∈ s, DifferentiableAt ℂ w z
  hasDerivAt_deriv : ∀ z ∈ s, HasDerivAt (deriv w) (-(p z * deriv w z) - r z * w z) z

/-! ### Heun's equation (§31.2) -/

/-- The exponent parameter `ε` determined by Fuchs's relation `α + β + 1 = γ + δ + ε`
(DLMF 31.2.1). -/
def heunEps (α β γ δ : ℂ) : ℂ := α + β + 1 - γ - δ

/-- The coefficient of `w'` in Heun's equation (DLMF 31.2.1):
`γ/z + δ/(z-1) + ε/(z-a)`. Junk values (division by zero) at `z ∈ {0, 1, a}`. -/
def heunCoeffP (a γ δ ε : ℂ) (z : ℂ) : ℂ := γ / z + δ / (z - 1) + ε / (z - a)

/-- The coefficient of `w` in Heun's equation (DLMF 31.2.1):
`(αβz - q)/(z(z-1)(z-a))`. Junk values at `z ∈ {0, 1, a}`. -/
def heunCoeffR (a q α β : ℂ) (z : ℂ) : ℂ := (α * β * z - q) / (z * (z - 1) * (z - a))

/-- DLMF 31.2.1, Heun's equation
`w'' + (γ/z + δ/(z-1) + ε/(z-a)) w' + (αβz - q)/(z(z-1)(z-a)) w = 0` on `s`. The Fuchs
relation `α + β + 1 = γ + δ + ε` is not built in; theorems assume it where DLMF does. The set
`s` should avoid the singular points `0, 1, a`. -/
@[dlmf 31.2.E1]
def IsHeunSolOn (a q α β γ δ ε : ℂ) (w : ℂ → ℂ) (s : Set ℂ) : Prop :=
  IsLinearODE2On (heunCoeffP a γ δ ε) (heunCoeffR a q α β) w s

/-- Heun's equation (DLMF 31.2.1) as a normalized operator for `Complex.linearODEValue`:
index `0` is the coefficient of `w`, index `1` that of `w'`. -/
def heunODECoeff (a q α β γ δ ε : ℂ) : Fin 2 → ℂ → ℂ :=
  ![heunCoeffR a q α β, heunCoeffP a γ δ ε]

/-- DLMF 31.2.4: the coefficient `A` of the normal form (31.2.3). -/
@[dlmf 31.2.E4]
def heunNormalA (a q γ δ ε : ℂ) : ℂ := -(γ * δ / 2) - γ * ε / (2 * a) + q / a

/-- DLMF 31.2.4: the coefficient `B` of the normal form (31.2.3). -/
@[dlmf 31.2.E4]
def heunNormalB (a q α β γ δ ε : ℂ) : ℂ :=
  γ * δ / 2 - δ * ε / (2 * (a - 1)) - (q - α * β) / (a - 1)

/-- DLMF 31.2.4: the coefficient `C` of the normal form (31.2.3). -/
@[dlmf 31.2.E4]
def heunNormalC (a q α β γ δ ε : ℂ) : ℂ :=
  γ * ε / (2 * a) + δ * ε / (2 * (a - 1)) - (a * α * β - q) / (a * (a - 1))

/-- DLMF 31.2.4: the coefficients `D, E, F` of the normal form, `D = ½γ(½γ - 1)` (with `γ`
replaced by `δ`, `ε` for `E`, `F`). -/
@[dlmf 31.2.E4]
def heunNormalD (γ : ℂ) : ℂ := γ / 2 * (γ / 2 - 1)

/-- DLMF 31.2.3: the right-hand side coefficient of the normal form
`W'' = (A/z + B/(z-1) + C/(z-a) + D/z² + E/(z-1)² + F/(z-a)²) W`. -/
@[dlmf 31.2.E3]
def heunNormalCoeff (a q α β γ δ ε : ℂ) (z : ℂ) : ℂ :=
  heunNormalA a q γ δ ε / z + heunNormalB a q α β γ δ ε / (z - 1) +
    heunNormalC a q α β γ δ ε / (z - a) + heunNormalD γ / z ^ 2 +
    heunNormalD δ / (z - 1) ^ 2 + heunNormalD ε / (z - a) ^ 2

/-! ### The local solution `Hl` (§31.3) -/

/-- DLMF 31.3.4: `P_j = (j - 1 + α)(j - 1 + β)`. -/
@[dlmf 31.3.E4]
def heunRecP (α β : ℂ) (j : ℕ) : ℂ := ((j : ℂ) - 1 + α) * ((j : ℂ) - 1 + β)

/-- DLMF 31.3.4: `Q_j = j((j - 1 + γ)(1 + a) + aδ + ε)`, with `ε = α + β + 1 - γ - δ`. -/
@[dlmf 31.3.E4]
def heunRecQ (a α β γ δ : ℂ) (j : ℕ) : ℂ :=
  (j : ℂ) * (((j : ℂ) - 1 + γ) * (1 + a) + a * δ + heunEps α β γ δ)

/-- DLMF 31.3.4: `R_j = a(j + 1)(j + γ)`. -/
@[dlmf 31.3.E4]
def heunRecR (a γ : ℂ) (j : ℕ) : ℂ := a * ((j : ℂ) + 1) * ((j : ℂ) + γ)

/-- The Maclaurin coefficients `c_j` of `Hl(a, q; α, β, γ, δ; z)` (DLMF 31.3.1–31.3.3):
`c₀ = 1`, `c₁ = q/(aγ)` and `c_{j+1} = ((Q_j + q)c_j - P_j c_{j-1})/R_j` for `j ≥ 1`. When a
denominator vanishes the totalized division gives `0`. -/
def heunLocalCoeff (a q α β γ δ : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => q / (a * γ)
  | (j + 2) => ((heunRecQ a α β γ δ (j + 1) + q) * heunLocalCoeff a q α β γ δ (j + 1) -
      heunRecP α β (j + 1) * heunLocalCoeff a q α β γ δ j) / heunRecR a γ (j + 1)

/-- The radius `min(1, |a|)` of the disk on which the Maclaurin series of `Hl` converges
(DLMF 31.3.1 with the singularities `1` and `a`; DLMF's standing assumption `|a| ≥ 1` makes it
`1`, but the eight local solutions of §31.3(ii) use parameters such as `1 - a` and `1/a`). -/
def heunLocalRadius (a : ℂ) : ℝ := min 1 ‖a‖

/-- DLMF 31.3.1: the local Heun function `Hl(a, q; α, β, γ, δ; z) = ∑_{j ≥ 0} c_j z^j`, the
solution of Heun's equation with exponent `0` at `z = 0` normalized by `Hl(0) = 1`; here
`ε = α + β + 1 - γ - δ`. Meaningful for `a ≠ 0`, `γ ∉ {0, -1, -2, …}` and
`|z| < min(1, |a|)`; elsewhere the `tsum` is a junk value. -/
@[dlmf 31.3.E1]
def heunLocal (a q α β γ δ : ℂ) (z : ℂ) : ℂ :=
  ∑' j : ℕ, heunLocalCoeff a q α β γ δ j * z ^ j

/-! ### Heun functions (§31.4) and polynomials (§31.5) -/

/-- DLMF 31.4.3 (finite singularities): `w` is a Heun function for the pair `s₁, s₂` on the
preconnected open set `U ∋ s₁, s₂`: a nontrivial solution of Heun's equation on `U` minus the
singular points that is analytic on all of `U`, in particular at `s₁` and `s₂`. DLMF also allows
`s = ∞` (a Fuchs–Frobenius solution at infinity); that case is not covered by this predicate. -/
@[dlmf 31.4.E3]
def IsHeunFunctionOn (a q α β γ δ ε : ℂ) (s₁ s₂ : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧ s₁ ∈ U ∧ s₂ ∈ U ∧ AnalyticOnNhd ℂ w U ∧
    IsHeunSolOn a q α β γ δ ε w (U \ {0, 1, a}) ∧ ∃ z ∈ U, w z ≠ 0

/-- §31.4: `q` is an eigenvalue `q_m` of the accessory parameter for the pair `(0, 1)`: the local
solution `Hl(a, q; α, β, γ, δ; ·)` continues analytically to a Heun function on a preconnected
open set containing `0` and `1`. -/
@[dlmf 31.4]
def IsHeunEigenvalue01 (a q α β γ δ : ℂ) : Prop :=
  ∃ (U : Set ℂ) (w : ℂ → ℂ), IsHeunFunctionOn a q α β γ δ (heunEps α β γ δ) 0 1 w U ∧
    w =ᶠ[𝓝 0] heunLocal a q α β γ δ

open Classical in
/-- DLMF 31.4.1: the Heun function `(0,1)Hf_m(a, q_m; α, β, γ, δ; z)`, the analytic continuation
of `Hl(a, q_m; α, β, γ, δ; z)` to the disk `|z| < |a|` when `q = q_m` is an eigenvalue. Defined by
choice of an analytic function on the disk agreeing with `Hl` near `0` (unique by the identity
theorem); `0` outside the disk or if no such continuation exists. The index `m` of DLMF is not
modelled: the eigenvalue `q` itself is the argument. -/
@[dlmf 31.4.E1]
def heunFunction01 (a q α β γ δ : ℂ) (z : ℂ) : ℂ :=
  if h : ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (Metric.ball 0 ‖a‖) ∧
      f =ᶠ[𝓝 0] heunLocal a q α β γ δ then
    if z ∈ Metric.ball (0 : ℂ) ‖a‖ then h.choose z else 0
  else 0

/-- The tails of the continued fraction (31.4.2): `heunCFTail a q α β γ δ m k` is
`R_k P_{k+1}/(Q_{k+1} + q - R_{k+1} P_{k+2}/(Q_{k+2} + q - ⋯))` truncated after `m` levels. -/
def heunCFTail (a q α β γ δ : ℂ) : ℕ → ℕ → ℂ
  | 0, _ => 0
  | (m + 1), k => heunRecR a γ k * heunRecP α β (k + 1) /
      (heunRecQ a α β γ δ (k + 1) + q - heunCFTail a q α β γ δ m (k + 1))

/-- DLMF 31.4.2: the `m`-th approximant of the continued fraction
`aγP₁/(Q₁ + q - R₁P₂/(Q₂ + q - R₂P₃/(Q₃ + q - ⋯)))`. -/
@[dlmf 31.4.E2]
def heunCFApprox (a q α β γ δ : ℂ) (m : ℕ) : ℂ :=
  a * γ * heunRecP α β 1 / (heunRecQ a α β γ δ 1 + q - heunCFTail a q α β γ δ m 1)

/-- DLMF 31.5.1: the `(n+1) × (n+1)` tridiagonal matrix with first row `(0, aγ, 0, …)` and row
`j ≥ 1` equal to `(…, P_j, -Q_j, R_j, …)` (columns `j - 1, j, j + 1`), for `α = -n`. Its
eigenvalues are the `q_{n,m}`, `m = 0, …, n`. -/
@[dlmf 31.5.E1]
def heunPolyMatrix (a β γ δ : ℂ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i k =>
    if (i : ℕ) = 0 then (if (k : ℕ) = 1 then a * γ else 0)
    else if (k : ℕ) + 1 = i then heunRecP (-(n : ℂ)) β i
    else if (k : ℕ) = i then -heunRecQ a (-(n : ℂ)) β γ δ i
    else if (k : ℕ) = i + 1 then heunRecR a γ i
    else 0

/-- DLMF 31.5.2: the Heun polynomial `Hp_{n,m}(a, q; -n, β, γ, δ; z)` as the truncation of the
series of `Hl(a, q; -n, β, γ, δ; z)` after degree `n`; for an eigenvalue `q = q_{n,m}` of
`heunPolyMatrix` the series terminates and `heunPoly` equals `Hl`. -/
@[dlmf 31.5.E2]
def heunPoly (a q β γ δ : ℂ) (n : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range (n + 1), C (heunLocalCoeff a q (-(n : ℂ)) β γ δ j) * X ^ j

/-! ### Expansions in series of hypergeometric functions (§31.11) -/

/-- DLMF 31.11.6 (as corrected in DLMF 1.1.7):
`K_j = (j+α-μ-1)(j+β-μ-1)(j+γ-μ-1)(j-μ)/((2j+λ-μ-1)(2j+λ-μ-2))`; `j` is complex so that
`j = -1` is allowed. -/
@[dlmf 31.11.E6]
def heunHypK (α β γ lam μ : ℂ) (j : ℂ) : ℂ :=
  (j + α - μ - 1) * (j + β - μ - 1) * (j + γ - μ - 1) * (j - μ) /
    ((2 * j + lam - μ - 1) * (2 * j + lam - μ - 2))

/-- DLMF 31.11.7: `L_j = a(λ+j)(μ-j) - q + (j+α-μ)(j+β-μ)(j+γ-μ)(j+λ)/((2j+λ-μ)(2j+λ-μ+1))
+ (j-α+λ)(j-β+λ)(j-γ+λ)(j-μ)/((2j+λ-μ)(2j+λ-μ-1))`. -/
@[dlmf 31.11.E7]
def heunHypL (a q α β γ lam μ : ℂ) (j : ℂ) : ℂ :=
  a * (lam + j) * (μ - j) - q +
    (j + α - μ) * (j + β - μ) * (j + γ - μ) * (j + lam) /
      ((2 * j + lam - μ) * (2 * j + lam - μ + 1)) +
    (j - α + lam) * (j - β + lam) * (j - γ + lam) * (j - μ) /
      ((2 * j + lam - μ) * (2 * j + lam - μ - 1))

/-- DLMF 31.11.8 (as corrected in DLMF 1.1.7):
`M_j = (j-α+λ+1)(j-β+λ+1)(j-γ+λ+1)(j+λ)/((2j+λ-μ+1)(2j+λ-μ+2))`. -/
@[dlmf 31.11.E8]
def heunHypM (α β γ lam μ : ℂ) (j : ℂ) : ℂ :=
  (j - α + lam + 1) * (j - β + lam + 1) * (j - γ + lam + 1) * (j + lam) /
    ((2 * j + lam - μ + 1) * (2 * j + lam - μ + 2))

/-- DLMF 31.11.4–31.11.5: the coefficients of the expansion 31.11.1, `c₀ = 1`,
`L₀c₀ + M₀c₁ = 0` and `K_j c_{j-1} + L_j c_j + M_j c_{j+1} = 0` (`j ≥ 1`), solved forward
(totalized division). -/
def heunHypCoeff (a q α β γ lam μ : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => -(heunHypL a q α β γ lam μ 0 / heunHypM α β γ lam μ 0)
  | (j + 2) => -((heunHypK α β γ lam μ ((j : ℂ) + 1) * heunHypCoeff a q α β γ lam μ j +
      heunHypL a q α β γ lam μ ((j : ℂ) + 1) * heunHypCoeff a q α β γ lam μ (j + 1)) /
      heunHypM α β γ lam μ ((j : ℂ) + 1))

/-- DLMF 31.11.3_1 (added in DLMF 1.1.7): the Fuchs–Frobenius solution at `∞` of the P-symbol
31.11.2, `P_j^5 = (λ)_j(1-γ+λ)_j/(1+λ-μ)_{2j} z^{-λ-j} ₂F₁(λ+j, 1-γ+λ+j; 1+λ-μ+2j; 1/z)`
(principal power, `|z| > 1`). -/
@[dlmf 31.11.E3_1]
def heunHypP5 (γ lam μ : ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  (ascPochhammer ℂ j).eval lam * (ascPochhammer ℂ j).eval (1 - γ + lam) /
      (ascPochhammer ℂ (2 * j)).eval (1 + lam - μ) * z ^ (-lam - j) *
    ordinaryHypergeometric (lam + j) (1 - γ + lam + j) (1 + lam - μ + 2 * j) (1 / z)

/-- DLMF 31.11.3_2 (added in DLMF 1.1.7): the other Fuchs–Frobenius solution at `∞`,
`P_j^6 = (λ-μ)_{2j}/((1-μ)_j(γ-μ)_j) z^{-μ+j} ₂F₁(μ-j, 1-γ+μ-j; 1-λ+μ-2j; 1/z)`. -/
@[dlmf 31.11.E3_2]
def heunHypP6 (γ lam μ : ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  (ascPochhammer ℂ (2 * j)).eval (lam - μ) /
      ((ascPochhammer ℂ j).eval (1 - μ) * (ascPochhammer ℂ j).eval (γ - μ)) * z ^ (-μ + j) *
    ordinaryHypergeometric (μ - j) (1 - γ + μ - j) (1 - lam + μ - 2 * j) (1 / z)

/-- The tails of the continued fraction 31.11.13:
`(K_k/M_k)/(L_k/M_k - (K_{k+1}/M_{k+1})/(L_{k+1}/M_{k+1} - ⋯))`, `m` levels. -/
def heunHypCFTail (a q α β γ lam μ : ℂ) : ℕ → ℕ → ℂ
  | 0, _ => 0
  | (m + 1), k => heunHypK α β γ lam μ k / heunHypM α β γ lam μ k /
      (heunHypL a q α β γ lam μ k / heunHypM α β γ lam μ k -
        heunHypCFTail a q α β γ lam μ m (k + 1))

/-- DLMF 31.11.13: the `m`-th approximant of
`L₀/M₀ - (K₁/M₁)/(L₁/M₁ - (K₂/M₂)/(L₂/M₂ - ⋯))`. -/
@[dlmf 31.11.E13]
def heunHypCFApprox (a q α β γ lam μ : ℂ) (m : ℕ) : ℂ :=
  heunHypL a q α β γ lam μ 0 / heunHypM α β γ lam μ 0 - heunHypCFTail a q α β γ lam μ m 1

/-! ### Contour integrals with continued branches, path-multiplicative solutions -/

/-- The branch of `u ↦ u ^ s` near `u = c ≠ 0` that takes the principal value `c ^ s` at `u = c`:
`exp(s (log c + log(u/c)))`, analytic for `u/c ∉ (-∞, 0]`. Used for integrands "with principal
values at the beginning" of a contour (DLMF 31.9.2). -/
def localBranchCpow (c s u : ℂ) : ℂ := cexp (s * (Complex.log c + Complex.log (u / c)))

/-- The Pochhammer double loop `(p₂+, p₁+, p₂-, p₁-)` based at `ζ`, parametrized by `[0, 1]`:
four full circles through `ζ`, centred at `p₂` (positive), `p₁` (positive), `p₂` (negative) and
`p₁` (negative). For `p₁ = 0`, `p₂ = 1` and `ζ ∈ (0, 1)` this is the contour `(1+, 0+, 1-, 0-)`
of DLMF 31.9.2 (compare Figure 5.12.3); it encloses no other singularity when the remaining
singular points lie outside both circles. -/
def pochhammerLoop (p₁ p₂ ζ : ℂ) (t : ℝ) : ℂ :=
  if t ≤ 1 / 4 then p₂ + (ζ - p₂) * cexp (2 * π * I * (4 * t))
  else if t ≤ 1 / 2 then p₁ + (ζ - p₁) * cexp (2 * π * I * (4 * t - 1))
  else if t ≤ 3 / 4 then p₂ + (ζ - p₂) * cexp (-(2 * π * I * (4 * t - 2)))
  else p₁ + (ζ - p₁) * cexp (-(2 * π * I * (4 * t - 3)))

open Classical in
/-- The integral `∫_γ f(t) dt` along a path `γ : [0, 1] → ℂ` of the analytic continuation along
`γ` of the germ of `f` at `γ 0`: the branches are continued continuously along the path and agree
with `f` at the beginning (DLMF 31.9.2, 31.10.1). The continuation is chosen (its values on the
path are unique); the integral is `0` if `f` does not continue along `γ`. -/
def continuedPathIntegral (γ : ℝ → ℂ) (f : ℂ → ℂ) : ℂ :=
  if h : ∃ F : ℝ → ℂ → ℂ, TauCeti.IsAnalyticContinuationAlong F γ (Icc 0 1) ∧
      F 0 =ᶠ[𝓝 (γ 0)] f then
    ∫ t in (0 : ℝ)..1, h.choose t (γ t) * deriv γ t
  else 0

/-- DLMF 31.6.1: `w` is path-multiplicative with exponent `ν` along the closed path `γ`: the
analytic continuation of the germ of `w` at `γ 0` along `γ` returns as `e^{2νπi} w`. DLMF takes
for `γ` a simple closed contour encircling the two singularities `s₁, s₂ ∈ {0, 1, a}` once in the
positive sense but not the third; that choice is left to the user of the predicate. -/
@[dlmf 31.6.E1]
def IsPathMultiplicative (γ : ℝ → ℂ) (ν : ℂ) (w : ℂ → ℂ) : Prop :=
  γ 1 = γ 0 ∧ ∃ F : ℝ → ℂ → ℂ, TauCeti.IsAnalyticContinuationAlong F γ (Icc 0 1) ∧
    F 0 =ᶠ[𝓝 (γ 0)] w ∧ F 1 =ᶠ[𝓝 (γ 0)] fun z => cexp (2 * ν * π * I) * w z

/-! ### Heun's operator (§31.10) -/

/-- DLMF 31.10.4: Heun's operator
`𝒟_z = z(z-1)(z-a) d²/dz² + (γ(z-1)(z-a) + δz(z-a) + εz(z-1)) d/dz + αβz`. Heun's equation is
`𝒟_z w = q w`. -/
@[dlmf 31.10.E4]
def heunOperator (a α β γ δ ε : ℂ) (w : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (z - 1) * (z - a) * deriv (deriv w) z +
    (γ * (z - 1) * (z - a) + δ * z * (z - a) + ε * z * (z - 1)) * deriv w z + α * β * z * w z

/-- DLMF 31.10.2: the weight `ρ(t) = t^{γ-1}(t-1)^{δ-1}(t-a)^{ε-1}` with principal powers (any
other branch is a constant multiple). -/
@[dlmf 31.10.E2]
def heunWeight (a γ δ ε : ℂ) (t : ℂ) : ℂ :=
  t ^ (γ - 1) * (t - 1) ^ (δ - 1) * (t - a) ^ (ε - 1)

/-- DLMF 31.10.6: `p(t) = t^γ (t-1)^δ (t-a)^ε = t(t-1)(t-a)ρ(t)`, principal powers. -/
@[dlmf 31.10.E6]
def heunConcomitantP (a γ δ ε : ℂ) (t : ℂ) : ℂ := t ^ γ * (t - 1) ^ δ * (t - a) ^ ε

/-! ### Confluent forms (§31.12) and ranks of irregular singularities -/

/-- DLMF 31.12.1, the confluent Heun equation
`w'' + (γ/z + δ/(z-1) + ε) w' + (αz - q)/(z(z-1)) w = 0`. -/
@[dlmf 31.12.E1]
def IsConfluentHeunSolOn (q α γ δ ε : ℂ) (w : ℂ → ℂ) (s : Set ℂ) : Prop :=
  IsLinearODE2On (fun z => γ / z + δ / (z - 1) + ε) (fun z => (α * z - q) / (z * (z - 1))) w s

/-- DLMF 31.12.2, the doubly-confluent Heun equation
`w'' + (δ/z² + γ/z + 1) w' + (αz - q)/z² w = 0`. -/
@[dlmf 31.12.E2]
def IsDoublyConfluentHeunSolOn (q α γ δ : ℂ) (w : ℂ → ℂ) (s : Set ℂ) : Prop :=
  IsLinearODE2On (fun z => δ / z ^ 2 + γ / z + 1) (fun z => (α * z - q) / z ^ 2) w s

/-- DLMF 31.12.3, the biconfluent Heun equation (sign as corrected in DLMF 1.0.7)
`w'' - (γ/z + δ + z) w' + (αz - q)/z w = 0`. -/
@[dlmf 31.12.E3]
def IsBiconfluentHeunSolOn (q α γ δ : ℂ) (w : ℂ → ℂ) (s : Set ℂ) : Prop :=
  IsLinearODE2On (fun z => -(γ / z + δ + z)) (fun z => (α * z - q) / z) w s

/-- DLMF 31.12.4, the triconfluent Heun equation `w'' + (γ + z) z w' + (αz - q) w = 0`. -/
@[dlmf 31.12.E4]
def IsTriconfluentHeunSolOn (q α γ : ℂ) (w : ℂ → ℂ) (s : Set ℂ) : Prop :=
  IsLinearODE2On (fun z => (γ + z) * z) (fun z => α * z - q) w s

/-- The equation `w'' + p w' + r w = 0` has an irregular singularity of rank `k ≥ 1` at infinity:
`k` is the least integer with `p(z) = O(z^{k-1})` and `r(z) = O(z^{2k-2})` as `z → ∞` (Poincaré's
rank; rank `0` would be an at most regular point). -/
def HasIrregularRankAtInfinity (p r : ℂ → ℂ) (k : ℕ) : Prop :=
  1 ≤ k ∧
    (p =O[Bornology.cobounded ℂ] fun z => z ^ ((k : ℤ) - 1)) ∧
    (r =O[Bornology.cobounded ℂ] fun z => z ^ (2 * (k : ℤ) - 2)) ∧
    ¬((p =O[Bornology.cobounded ℂ] fun z => z ^ ((k : ℤ) - 2)) ∧
      (r =O[Bornology.cobounded ℂ] fun z => z ^ (2 * (k : ℤ) - 4)))

/-- The equation `w'' + p w' + r w = 0` has an irregular singularity of rank `k ≥ 1` at the
finite point `z₀`: `k` is the least integer with `p(z) = O((z-z₀)^{-k-1})` and
`r(z) = O((z-z₀)^{-2k-2})` as `z → z₀` (the image of `HasIrregularRankAtInfinity` under
`z - z₀ = 1/u`). -/
def HasIrregularRankAt (p r : ℂ → ℂ) (z₀ : ℂ) (k : ℕ) : Prop :=
  1 ≤ k ∧
    (p =O[𝓝[≠] z₀] fun z => (z - z₀) ^ (-(k : ℤ) - 1)) ∧
    (r =O[𝓝[≠] z₀] fun z => (z - z₀) ^ (-2 * (k : ℤ) - 2)) ∧
    ¬((p =O[𝓝[≠] z₀] fun z => (z - z₀) ^ (-(k : ℤ))) ∧
      (r =O[𝓝[≠] z₀] fun z => (z - z₀) ^ (-2 * (k : ℤ))))

/-! ### The general Fuchsian equation (§31.14) and Stieltjes polynomials (§31.15) -/

/-- DLMF 31.14.1: the coefficient `∑_j γ_j/(z - a_j)` of `w'` in the general Fuchsian equation
with finite singularities `a_1, …, a_N`. -/
def fuchsianCoeffP {N : ℕ} (a γ : Fin N → ℂ) (z : ℂ) : ℂ := ∑ j, γ j / (z - a j)

/-- DLMF 31.14.1: the coefficient `∑_j q_j/(z - a_j)` of `w` in the general Fuchsian equation. -/
def fuchsianCoeffR {N : ℕ} (a q : Fin N → ℂ) (z : ℂ) : ℂ := ∑ j, q j / (z - a j)

/-- DLMF 31.14.1: the general second-order Fuchsian equation with regular singularities at the
`a_j` and at `∞`,
`w'' + (∑_j γ_j/(z - a_j)) w' + (∑_j q_j/(z - a_j)) w = 0`, `∑_j q_j = 0` (the last condition is
a hypothesis of the theorems, not part of the predicate). -/
@[dlmf 31.14.E1]
def IsFuchsianSolOn {N : ℕ} (a γ q : Fin N → ℂ) (w : ℂ → ℂ) (s : Set ℂ) : Prop :=
  IsLinearODE2On (fuchsianCoeffP a γ) (fuchsianCoeffR a q) w s

/-- DLMF 31.14.5: `q̃_j = ½ ∑_{k ≠ j} γ_j γ_k/(a_j - a_k) - q_j`. -/
@[dlmf 31.14.E5]
def fuchsianNormalQ {N : ℕ} (a γ q : Fin N → ℂ) (j : Fin N) : ℂ :=
  (1 / 2) * ∑ k ∈ Finset.univ.erase j, γ j * γ k / (a j - a k) - q j

/-- DLMF 31.14.5: `γ̃_j = (γ_j/2)(γ_j/2 - 1)`. -/
@[dlmf 31.14.E5]
def fuchsianNormalGamma {N : ℕ} (γ : Fin N → ℂ) (j : Fin N) : ℂ := γ j / 2 * (γ j / 2 - 1)

/-- DLMF 31.14.4: the right-hand side coefficient `∑_j (γ̃_j/(z - a_j)² + q̃_j/(z - a_j))` of the
normal form `W'' = (…) W`. -/
@[dlmf 31.14.E4]
def fuchsianNormalCoeff {N : ℕ} (a γ q : Fin N → ℂ) (z : ℂ) : ℂ :=
  ∑ j, (fuchsianNormalGamma γ j / (z - a j) ^ 2 + fuchsianNormalQ a γ q j / (z - a j))

/-- The polynomial `∏_j (X - a_j)`. -/
def fuchsianPi {N : ℕ} (a : Fin N → ℂ) : ℂ[X] := ∏ j, (X - C (a j))

/-- The polynomial `∑_j γ_j ∏_{k ≠ j} (X - a_k)`, i.e. `∏_k (X - a_k) · ∑_j γ_j/(X - a_j)`. -/
def fuchsianGammaPoly {N : ℕ} (a γ : Fin N → ℂ) : ℂ[X] :=
  ∑ j, C (γ j) * ∏ k ∈ Finset.univ.erase j, (X - C (a k))

/-- DLMF 31.15.1 cleared of denominators: the polynomial `S` solves
`w'' + (∑_j γ_j/(z - a_j)) w' + Φ(z)/∏_j (z - a_j) w = 0`, i.e.
`∏(X - a_j) S'' + (∑_j γ_j ∏_{k≠j}(X - a_k)) S' + Φ S = 0`. -/
@[dlmf 31.15.E1]
def IsStieltjesEquation {N : ℕ} (a γ : Fin N → ℂ) (Φ S : ℂ[X]) : Prop :=
  fuchsianPi a * derivative (derivative S) + fuchsianGammaPoly a γ * derivative S + Φ * S = 0

/-- §31.15(i): `V` is a Van Vleck polynomial with Stieltjes polynomial `S` of degree `n`:
`deg V ≤ N - 2`, `deg S = n` and (31.15.1) holds with `Φ = V`. -/
@[dlmf 31.15.i]
def IsVanVleckStieltjes {N : ℕ} (a γ : Fin N → ℂ) (n : ℕ) (V S : ℂ[X]) : Prop :=
  V.natDegree ≤ N - 2 ∧ S.natDegree = n ∧ S ≠ 0 ∧ IsStieltjesEquation a γ V S

/-- DLMF 31.15.4: `G(ζ_1, …, ζ_n) = ∏_k ∏_ℓ (ζ_k - a_ℓ)^{γ_ℓ/2} ∏_{j > k} (ζ_k - ζ_j)`, principal
powers. -/
@[dlmf 31.15.E4]
def stieltjesG {N n : ℕ} (a γ : Fin N → ℂ) (ζ : Fin n → ℂ) : ℂ :=
  ∏ k, ((∏ ℓ, (ζ k - a ℓ) ^ (γ ℓ / 2)) * ∏ j ∈ Finset.univ.filter (fun j => k < j), (ζ k - ζ j))

/-- The number of zeros of `S` (with multiplicity) in the open real interval `(x, y)`. -/
def rootsIn (S : ℂ[X]) (x y : ℝ) : ℕ :=
  (S.roots.filter fun z => z.im = 0 ∧ x < z.re ∧ z.re < y).card

/-- §31.15(iii): `S` is a monic Stieltjes polynomial with zero distribution `m`: it has degree
`n = ∑ m_j` with exactly `m_j` zeros in `(a_j, a_{j+1})`, for real increasing `a_j`. -/
def IsStieltjesOfIndex {N : ℕ} (a γ : Fin (N + 1) → ℝ) (m : Fin N → ℕ) (S : ℂ[X]) : Prop :=
  S.Monic ∧ (∃ V : ℂ[X], IsVanVleckStieltjes (fun j => (a j : ℂ)) (fun j => (γ j : ℂ))
      (∑ j, m j) V S) ∧
    ∀ j : Fin N, rootsIn S (a j.castSucc) (a j.succ) = m j

open Classical in
/-- §31.15(iii): the Stieltjes polynomial `S_𝐦` with `m_j` zeros in `(a_j, a_{j+1})`, defined by
choice when it exists uniquely (DLMF: always, under 31.15.5–31.15.6), and `0` otherwise. -/
@[dlmf 31.15.iii]
def stieltjesPoly {N : ℕ} (a γ : Fin (N + 1) → ℝ) (m : Fin N → ℕ) : ℂ[X] :=
  if h : ∃! S, IsStieltjesOfIndex a γ m S then h.exists.choose else 0

/-- DLMF 31.15.10: the box `Q = (a_1, a_2) × ⋯ × (a_{N-1}, a_N)` (here indexed from `0`). -/
@[dlmf 31.15.E10]
def stieltjesBox {N : ℕ} (a : Fin (N + 1) → ℝ) : Set (Fin N → ℝ) :=
  Set.univ.pi fun j => Ioo (a j.castSucc) (a j.succ)

/-- DLMF 31.15.12: the weight
`ρ(z) = ∏_j ∏_k |z_j - a_k|^{γ_k - 1} · ∏_{j<k} (z_k - z_j)` on `Q`. -/
@[dlmf 31.15.E12]
def stieltjesWeight {N : ℕ} (a γ : Fin (N + 1) → ℝ) (z : Fin N → ℝ) : ℝ :=
  (∏ j, ∏ k, |z j - a k| ^ (γ k - 1)) *
    ∏ j, ∏ k ∈ Finset.univ.filter (fun k => j < k), (z k - z j)

/-- DLMF 31.15.8: the product `S_𝐦(z_1) ⋯ S_𝐦(z_{N-1})`. -/
@[dlmf 31.15.E8]
def stieltjesProduct {N : ℕ} (a γ : Fin (N + 1) → ℝ) (m : Fin N → ℕ) (z : Fin N → ℝ) : ℂ :=
  ∏ j, (stieltjesPoly a γ m).eval (z j : ℂ)

/-- DLMF 31.15.11: the inner product `(f, g)_ρ = ∫_Q f(z) conj(g(z)) ρ(z) dz`. -/
@[dlmf 31.15.E11]
def stieltjesInner {N : ℕ} (a γ : Fin (N + 1) → ℝ) (f g : (Fin N → ℝ) → ℂ) : ℂ :=
  ∫ z in stieltjesBox a, f z * (starRingEnd ℂ) (g z) * (stieltjesWeight a γ z : ℂ)

end DLMF.Heun
