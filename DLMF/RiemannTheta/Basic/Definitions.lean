/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Basic.Theta
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Riemann matrices, theta series and characteristics
-/

@[expose] public noncomputable section

open Complex Matrix Finset Filter Topology
open scoped Real

variable {ι : Type*} [Fintype ι]

namespace DLMF.RiemannTheta

/-- The Siegel upper half-space: complex symmetric matrices with positive definite imaginary
part, i.e. DLMF's *Riemann matrices* `Ω` (DLMF §21.1, Notation). -/
@[dlmf 21.1 "Riemann matrix: complex symmetric with strictly positive definite imaginary part"]
def siegelUpperHalfSpace (ι : Type*) [Fintype ι] : Set (Matrix ι ι ℂ) :=
  {Ω | Ωᵀ = Ω ∧ (Ω.map Complex.im).PosDef}

/-- The `n`-th term `exp(2πi(½ n·Ω·n + n·z))` of the Riemann theta series (DLMF 21.2.1). -/
def riemannThetaTerm (z : ι → ℂ) (Ω : Matrix ι ι ℂ) (n : ι → ℤ) : ℂ :=
  cexp (2 * π * I * ((1 / 2 : ℂ) * ((fun i => (n i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ))) +
    (fun i => (n i : ℂ)) ⬝ᵥ z))

/-- The Riemann theta function `θ(z|Ω) = ∑_{n ∈ ℤ^g} exp(2πi(½ n·Ω·n + n·z))` (DLMF 21.2.1).
The `tsum` is the genuine sum for `Ω ∈ siegelUpperHalfSpace ι` (`hasSum_riemannTheta`). -/
@[dlmf 21.2.E1]
def riemannTheta (z : ι → ℂ) (Ω : Matrix ι ι ℂ) : ℂ :=
  ∑' n : ι → ℤ, riemannThetaTerm z Ω n

/-- The term of the theta series with characteristics (DLMF 21.2.5):
`exp(2πi(½ [n+α]·Ω·[n+α] + [n+α]·[z+β]))`. -/
def riemannThetaCharTerm (α β : ι → ℝ) (z : ι → ℂ) (Ω : Matrix ι ι ℂ) (n : ι → ℤ) : ℂ :=
  cexp (2 * π * I * ((1 / 2 : ℂ) * ((fun i => (n i : ℂ) + α i) ⬝ᵥ
      (Ω *ᵥ fun i => (n i : ℂ) + α i)) +
    (fun i => (n i : ℂ) + α i) ⬝ᵥ (fun i => z i + β i)))

/-- The Riemann theta function with characteristics `[α; β]`, `α, β ∈ ℝ^g` (DLMF 21.2.5). -/
@[dlmf 21.2.E5]
def riemannThetaChar (α β : ι → ℝ) (z : ι → ℂ) (Ω : Matrix ι ι ℂ) : ℂ :=
  ∑' n : ι → ℤ, riemannThetaCharTerm α β z Ω n

/-- The scaled Riemann theta function
`θ̂(z|Ω) = exp(-π [Im z]·[Im Ω]⁻¹·[Im z]) θ(z|Ω)` (DLMF 21.2.2). -/
@[dlmf 21.2.E2]
def riemannThetaScaled [DecidableEq ι] (z : ι → ℂ) (Ω : Matrix ι ι ℂ) : ℂ :=
  (Real.exp (-π * ((fun i => (z i).im) ⬝ᵥ ((Ω.map Complex.im)⁻¹ *ᵥ fun i => (z i).im))) : ℂ) *
    riemannTheta z Ω

/-- The alternative normalization `Θ(φ|B) = θ(φ/(2πi) | B/(2πi))` (DLMF §21.1). -/
@[dlmf 21.1 "Θ(φ|B) = θ(φ/(2πi)|B/(2πi)); the series form is riemannThetaBig_eq_tsum"]
def riemannThetaBig (φ : ι → ℂ) (B : Matrix ι ι ℂ) : ℂ :=
  riemannTheta (fun i => φ i / (2 * π * I)) ((2 * π * I)⁻¹ • B)

/-- Positivity of the quadratic form of `Im Ω` on nonzero real vectors. This open condition
holds on the Siegel upper half-space and does not require `Ω` to be symmetric. -/
def Rth21PosIm (Ω : Matrix ι ι ℂ) : Prop :=
  ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (Ω.map Complex.im *ᵥ x)

/-- The Riemann matrix `[[i, -1/2], [-1/2, i]]` of DLMF 21.2.3 (also `Ω₁` of 21.4.2). -/
@[dlmf 21.2.E3 "the example Riemann matrix"]
def riemannMatrixExample : Matrix (Fin 2) (Fin 2) ℂ := !![I, -1 / 2; -1 / 2, I]

/-- The `3 × 3` Riemann matrix `Ω₂` of DLMF 21.4.3 (graphics section; exact matrix retained). -/
@[dlmf 21.4.E3]
def riemannMatrixOmegaTwo : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-1 / 2 + I, 1 / 2 - 1 / 2 * I, -1 / 2 - 1 / 2 * I;
     1 / 2 - 1 / 2 * I, I, 0;
     -1 / 2 - 1 / 2 * I, 0, I]

/-- The set of half-period characteristics `[α; β]`, `αᵢ, βᵢ ∈ {0, ½}` (DLMF §21.2(ii)). -/
@[dlmf 21.2.ii "half-period characteristics"]
def halfPeriodCharacteristics (ι : Type*) : Set ((ι → ℝ) × (ι → ℝ)) :=
  {c | ∀ i, (c.1 i = 0 ∨ c.1 i = 1 / 2) ∧ (c.2 i = 0 ∨ c.2 i = 1 / 2)}

end DLMF.RiemannTheta
