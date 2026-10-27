/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Asymptotics of integrals: definitions (DLMF §§2.3–2.4)

* `variationalOperator a b f` (2.3.6): `𝒱_{a,b}(f) = ∫ₐᵇ |f'(t)| dt`.
* `binomSeriesCoeff p β n` and `laplaceCoeff L₀ p q λ μ s` (2.3.16–2.3.18, 2.4.12–2.4.13):
  the coefficients `bₛ` of Laplace's method, defined by the residue formula 2.3.18 in its
  formal form `bₛ = μ⁻¹ [τˢ] Q(τ) P(τ)^{-(λ+s)/μ}`, where `p(t) - p(a) = (t-a)^μ P(t-a)` and
  `q(t) = (t-a)^{λ-1} Q(t-a)`. The power `p₀^{-(λ+s)/μ}` is `exp(-(λ+s)/μ · L₀)` for a chosen
  logarithm `L₀` of `p₀` (for `p₀ > 0` the real logarithm; in §2.4(iii) the branch with
  `|θ + μω + ph p₀| ≤ ½π`, 2.4.13), and `(P/p₀)^β` is the binomial series.
* `bromwichPartial Q σ t η` (2.4.3, 2.4.6): the truncated inversion integral
  `(2πi)⁻¹ ∫_{σ-iη}^{σ+iη} e^{tz} Q(z) dz`.
* `stationaryPhaseP p q s` (2.3.21): `Pₛ = ((1/p') d/dt)ˢ (q/p')`.
* `bleisteinA`, `bleisteinB`, `bleisteinW`, `bleisteinF` (2.3.26, 2.3.27, 2.3.33): the
  quadratic change of variable of Bleistein's method and its comparison integrals.
-/

@[expose] public noncomputable section

open Finset MeasureTheory

namespace DLMF.AsymptoticApproximations

/-- DLMF 2.3.6: the variational operator `𝒱_{a,b}(f) = ∫ₐᵇ |f'(t)| dt` (for `f` of class `C¹`
on `[a, b]` this is the total variation of §1.4(v)). For `b = ∞` the statements use
`∫_{(a,∞)} |f'(t)| dt` directly. -/
@[dlmf 2.3.E6]
def variationalOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : ℝ)
    (f : ℝ → E) : ℝ :=
  ∫ t in a..b, ‖deriv f t‖

/-- The binomial coefficient `(β choose k) = β(β-1)⋯(β-k+1)/k!` for complex `β`. -/
def cbinom (β : ℂ) (k : ℕ) : ℂ :=
  (descPochhammer ℂ k).eval β / (k.factorial : ℂ)

/-- The coefficient `[τⁿ] (P(τ)/p₀)^β` of the binomial series, where `P(τ) = ∑ pₖ τᵏ` with
`p₀ ≠ 0`: `(P/p₀)^β = ∑ₖ (β choose k) (P/p₀ - 1)ᵏ`, and `P/p₀ - 1` has no constant term, so only
`k ≤ n` contributes to `[τⁿ]`. -/
def binomSeriesCoeff (p : ℕ → ℂ) (β : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ range (n + 1), cbinom β k *
    PowerSeries.coeff n ((PowerSeries.mk fun j => if j = 0 then 0 else p j / p 0) ^ k)

/-- DLMF 2.3.18 (formal residue form, defining the `bₛ` of 2.3.15–2.3.16):
`bₛ = μ⁻¹ Res_{t=a}[q(t)/(p(t) - p(a))^{(λ+s)/μ}]
= μ⁻¹ p₀^{-(λ+s)/μ} [τˢ] Q(τ)(P(τ)/p₀)^{-(λ+s)/μ}`,
for `p(t) - p(a) = ∑ pₖ (t-a)^{k+μ}` and `q(t) = ∑ qₖ (t-a)^{k+λ-1}` (2.3.14, 2.4.11). The power
of `p₀` is `exp(-(λ+s)/μ · L₀)` with `exp L₀ = p₀` (the theorems carry this hypothesis). -/
@[dlmf 2.3.E18]
def laplaceCoeff (L₀ : ℂ) (p q : ℕ → ℂ) (lam mu : ℂ) (s : ℕ) : ℂ :=
  mu⁻¹ * Complex.exp (-((lam + s) / mu) * L₀) *
    ∑ j ∈ range (s + 1), q j * binomSeriesCoeff p (-((lam + s) / mu)) (s - j)

/-- DLMF 2.4.3, 2.4.6: the truncated inversion integral
`(2πi)⁻¹ ∫_{σ-iη}^{σ+iη} e^{tz} Q(z) dz = (2π)⁻¹ ∫_{-η}^{η} e^{t(σ+iτ)} Q(σ+iτ) dτ`
(path `z = σ + iτ`, `dz = i dτ`). -/
def bromwichPartial (Q : ℂ → ℂ) (σ t η : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ τ in -η..η, Complex.exp (t * (σ + τ * Complex.I)) * Q (σ + τ * Complex.I)

/-- DLMF 2.3.21: `Pₛ(t) = ((1/p'(t)) d/dt)ˢ (q(t)/p'(t))`, `s = 0, 1, 2, …`. -/
@[dlmf 2.3.E21]
def stationaryPhaseP (p : ℝ → ℝ) (q : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => fun t => q t / Complex.ofReal (deriv p t)
  | s + 1 => fun t => deriv (stationaryPhaseP p q s) t / Complex.ofReal (deriv p t)

/-- DLMF 2.3.26: `a(α) = ±(2p(α,0) - 2p(α,α))^{1/2}`, the sign being that of `α` (`+` for
`α ≥ 0`). DLMF prints the square root without a sign; the sign of `α` is needed for the
requirement stated before 2.3.26 that `t = 0` correspond to `w = 0` under 2.3.27 when `α < 0`
(`bleisteinW_zero`). The function `p` is `p α t`, with minimum of `p(α, ·)` at `t = α`. -/
@[dlmf 2.3.E26]
def bleisteinA (p : ℝ → ℝ → ℝ) (α : ℝ) : ℝ :=
  if 0 ≤ α then Real.sqrt (2 * p α 0 - 2 * p α α) else -Real.sqrt (2 * p α 0 - 2 * p α α)

/-- DLMF 2.3.26: `b(α) = p(α, 0)`. -/
@[dlmf 2.3.E26]
def bleisteinB (p : ℝ → ℝ → ℝ) (α : ℝ) : ℝ :=
  p α 0

/-- DLMF 2.3.27: the new variable `w = a(α) ± (2p(α,t) - 2p(α,α))^{1/2}`, upper sign for
`t > α`, lower sign for `t < α` (at `t = α` both give `w = a`); DLMF writes
`a = (2p(α,0) - 2p(α,α))^{1/2}`, see `bleisteinA` for the sign. -/
@[dlmf 2.3.E27]
def bleisteinW (p : ℝ → ℝ → ℝ) (α t : ℝ) : ℝ :=
  if α ≤ t then bleisteinA p α + Real.sqrt (2 * p α t - 2 * p α α)
  else bleisteinA p α - Real.sqrt (2 * p α t - 2 * p α α)

/-- DLMF 2.3.33: `Fₛ(y) = ∫₀^∞ exp(-½τ² + yτ) (τ - y)ˢ τ^{λ-1} dτ` (`λ > 0`). -/
@[dlmf 2.3.E33]
def bleisteinF (lam : ℝ) (s : ℕ) (y : ℝ) : ℝ :=
  ∫ τ in Set.Ioi (0 : ℝ), Real.exp (-(τ ^ 2 / 2) + y * τ) * (τ - y) ^ s * τ ^ (lam - 1)

/-- The power `(γ(u) - a)^ν = |γ(u) - a|^ν e^{iνθ(u)}` along a path with the branch `θ` of
`ph(γ(u) - a)` (DLMF §2.4(iii)(a)). -/
def pathPow (γ : ℝ → ℂ) (θ : ℝ → ℝ) (a ν : ℂ) (u : ℝ) : ℂ :=
  (‖γ u - a‖ : ℂ) ^ ν * Complex.exp (ν * (θ u * Complex.I))

/-- The scale `z^{-ν} e^{-zp(a)}` for `z = r e^{iθ}`, written in polar coordinates
`(r, θ)` so that `z^{-ν} = r^{-ν} e^{-iνθ}` (DLMF 2.4.12). -/
def polarScale (pa : ℂ) (ν : ℂ) (rθ : ℝ × ℝ) : ℂ :=
  Complex.exp (-(rθ.1 * Complex.exp (rθ.2 * Complex.I)) * pa) * (rθ.1 : ℂ) ^ (-ν) *
    Complex.exp (-ν * (rθ.2 * Complex.I))

end DLMF.AsymptoticApproximations
