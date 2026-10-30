/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Asymptotic expansions: definitions (DLMF §2.1)

The order symbols of DLMF §2.1(i) are Mathlib's `Asymptotics.IsBigO`, `Asymptotics.IsLittleO`
and `Asymptotics.IsEquivalent` along a filter; "as `x → c` in `𝐗`" is the filter `𝓝[𝐗] c`
for a finite limit point `c`, and `cobounded 𝕜 ⊓ 𝓟 𝐗` for `x → ∞` in `𝐗`. The asymptotic
scales of §2.1(v) are the project's `Asymptotics.IsAsymptoticScale`, and the expansions with
respect to a scale with constant coefficients are `Asymptotics.HasAsymptoticExpansion`
(`DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion`).

This file adds the specific forms of DLMF §2.1(iii)–(v):

* `HasPoincareExpansion 𝐗 a f` (2.1.13–2.1.14): `f(x) ~ ∑ aₛ x⁻ˢ` as `x → ∞` in `𝐗`;
* `HasPoincareExpansionAt 𝐗 c a f` (2.1.16): `f(x) ~ ∑ aₛ (x - c)ˢ` as `x → c` in `𝐗`;
* `HasUniformPoincareExpansion 𝐔 𝐗 a f` (2.1.18): the expansion holds uniformly in a
  parameter `u ∈ 𝐔`, with coefficients `aₛ(u)`;
* `HasGeneralizedAsymptoticExpansion l φ fs f` (2.1.19–2.1.21): `f ~ ∑ fₛ; {φₛ}` along `l`.

For §2.2 it also defines `lagrangeReversionCoeff`, the coefficients `Fₛ` of Lagrange's formula
2.2.8 for the reversion of `f(x) ~ x + f₀ + f₁x⁻¹ + ⋯`.
-/

@[expose] public noncomputable section

open Filter Finset Asymptotics Bornology
open scoped Topology

namespace DLMF.AsymptoticApproximations

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- DLMF 2.1.13–2.1.14: the Poincaré asymptotic expansion `f(x) ~ a₀ + a₁x⁻¹ + a₂x⁻² + ⋯` as
`x → ∞` in the set `𝐗 ⊆ 𝕜` (`𝕜 = ℝ` or `ℂ`): for every `n`,
`f(x) = ∑_{s<n} aₛ x⁻ˢ + O(x⁻ⁿ)` along `cobounded 𝕜 ⊓ 𝓟 𝐗`. The case `n = 0` (`f = O(1)`)
follows from `n = 1`, so this agrees with DLMF's "for each positive integer `n`". The
coefficients may lie in any normed space over `𝕜`. When `𝐗` is bounded the filter is `⊥` and
the condition is vacuous; DLMF assumes `𝐗` unbounded. -/
@[dlmf 2.1.E13, dlmf 2.1.E14]
def HasPoincareExpansion (X : Set 𝕜) (a : ℕ → E) (f : 𝕜 → E) : Prop :=
  HasAsymptoticExpansion (cobounded 𝕜 ⊓ 𝓟 X) (fun n x => x⁻¹ ^ n) a f

/-- DLMF 2.1.16: the asymptotic expansion `f(x) ~ a₀ + a₁(x - c) + a₂(x - c)² + ⋯` as `x → c`
in `𝐗`: for each `n` the difference between `f(x)` and the `n`th partial sum is
`O((x - c)ⁿ)` along `𝓝[𝐗] c`. DLMF assumes that `c` is a limit point of `𝐗`. -/
@[dlmf 2.1.E16]
def HasPoincareExpansionAt (X : Set 𝕜) (c : 𝕜) (a : ℕ → E) (f : 𝕜 → E) : Prop :=
  HasAsymptoticExpansion (𝓝[X] c) (fun n x => (x - c) ^ n) a f

/-- DLMF 2.1.18 (with the bound of §2.1(iv)): `f(u, x) ~ ∑ aₛ(u) x⁻ˢ` as `x → ∞` in `𝐗`,
uniformly with respect to `u ∈ 𝐔`. The `O`-symbol is taken along the product filter
`𝓟 𝐔 ×ˢ (cobounded 𝕜 ⊓ 𝓟 𝐗)`, so the implied constant and the threshold for `|x|` do not depend
on `u`; `hasUniformPoincareExpansion_iff` restates this as the explicit bound of DLMF. -/
@[dlmf 2.1.E18]
def HasUniformPoincareExpansion {ι : Type*} (U : Set ι) (X : Set 𝕜) (a : ℕ → ι → E)
    (f : ι → 𝕜 → E) : Prop :=
  ∀ n : ℕ, (fun p : ι × 𝕜 => f p.1 p.2 - ∑ s ∈ range n, p.2⁻¹ ^ s • a s p.1)
    =O[𝓟 U ×ˢ (cobounded 𝕜 ⊓ 𝓟 X)] fun p => p.2⁻¹ ^ n

/-- DLMF 2.1.19–2.1.21: `∑ fₛ(x)` is a generalized asymptotic expansion of `f(x)` with respect
to the scale `{φₛ(x)}` along the filter `l` (DLMF: as `x → c` in `𝐗`): the `φₛ` form an
asymptotic scale, `φₛ₊₁ = o(φₛ)` (2.1.19), and `f = ∑_{s<n} fₛ + O(φₙ)` for every `n`
(2.1.20). The notation of 2.1.21 is this predicate. -/
@[dlmf 2.1.E19, dlmf 2.1.E20, dlmf 2.1.E21]
def HasGeneralizedAsymptoticExpansion {α : Type*} (l : Filter α) (φ : ℕ → α → 𝕜)
    (fs : ℕ → α → E) (f : α → E) : Prop :=
  IsAsymptoticScale l φ ∧ ∀ n : ℕ, (fun x => f x - ∑ s ∈ range n, fs s x) =O[l] φ n

/-- DLMF 2.2.8 (Lagrange's formula for the reversion of series): the coefficients `Fₛ` in
`x ∼ y - F₀ - F₁y⁻¹ - F₂y⁻² - ⋯` for the root of `f(x) = y`, where
`f(x) ∼ x + f₀ + f₁x⁻¹ + f₂x⁻² + ⋯` (2.2.7): `F₀ = f₀`, and for `s ≥ 1`, `sFₛ` is the coefficient
of `x⁻¹` in the expansion of `f(x)ˢ`. Writing `f(x) = x(1 + X·∑ fₖ Xᵏ)` with `X = x⁻¹`, that
coefficient is `[X^{s+1}] (1 + X·∑ fₖ Xᵏ)ˢ`. Here `lagrangeReversionCoeff fc s` is `Fₛ`. -/
@[dlmf 2.2.E8]
def lagrangeReversionCoeff {R : Type*} [Field R] (fc : ℕ → R) : ℕ → R
  | 0 => fc 0
  | s + 1 => ((s + 1 : ℕ) : R)⁻¹ *
      PowerSeries.coeff (s + 2) ((1 + PowerSeries.X * PowerSeries.mk fc) ^ (s + 1))

/-- The `n`th remainder `f(x) - ∑_{s<n} aₛ x⁻ˢ` of a Poincaré expansion. -/
def poincareRemainder (a : ℕ → E) (f : 𝕜 → E) (n : ℕ) (x : 𝕜) : E :=
  f x - ∑ s ∈ range n, x⁻¹ ^ s • a s

/-- The open sector `{z : R < |z|, |ph(z e^{-iθ})| < ω}` with vertex `0`, bisector `ph z = θ`
and half-opening `ω`, used for Ritt's theorem. -/
def rittSector (θ ω R : ℝ) : Set ℂ :=
  {z | R < ‖z‖ ∧ |Complex.arg (z * Complex.exp (-(θ * Complex.I)))| < ω}

/-- The closed sector `{z : |ph(z e^{-iθ})| ≤ ω}`. -/
def rittClosedSector (θ ω : ℝ) : Set ℂ :=
  {z | |Complex.arg (z * Complex.exp (-(θ * Complex.I)))| ≤ ω}

end DLMF.AsymptoticApproximations
