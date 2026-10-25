/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Theta functions: integrals (DLMF §20.10)

Mellin transforms (20.10.1–20.10.3) and Laplace transforms (20.10.4–20.10.5) with respect to the
lattice parameter. Integrals are Bochner integrals over `(0, ∞)` and are stated together with
integrability, so that Lean's convention `∫ = 0` for non-integrable functions plays no role.
Powers `x^{s-1}`, `2^s`, `π^{-s/2}` and `√s` are principal complex powers.

**Exceptional point (20.10.3).** For `Re s > 0` the right side `(1 - 2^{1-s}) π^{-s/2} Γ(s/2) ζ(s)`
is meant as its analytic continuation, which is removable at `s = 1`, where Mathlib's totalized
`riemannZeta 1` gives the wrong value `0`. We state 20.10.3 for `s ≠ 1` and the value at `s = 1`,
`∫₀^∞ (1 - θ₄(0|ix²)) dx = ln 2`, separately.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic

/-- DLMF 20.10.1: `∫₀^∞ x^{s-1} θ₂(0|ix²) dx = (2^s - 1) π^{-s/2} Γ(s/2) ζ(s)`, `Re s > 1`. -/
@[dlmf 20.10.E1]
theorem mellin_jacobiThetaTwoNullTau {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * jacobiThetaTwoNullTau (I * x ^ 2))
        (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * jacobiThetaTwoNullTau (I * x ^ 2) =
        (2 ^ s - 1) * (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s := by
  sorry

/-- DLMF 20.10.2: `∫₀^∞ x^{s-1} (θ₃(0|ix²) - 1) dx = π^{-s/2} Γ(s/2) ζ(s)`, `Re s > 1`. -/
@[dlmf 20.10.E2]
theorem mellin_jacobiThetaThreeNullTau_sub_one {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * (jacobiThetaThreeNullTau (I * x ^ 2) - 1))
        (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * (jacobiThetaThreeNullTau (I * x ^ 2) - 1) =
        (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s := by
  sorry

/-- DLMF 20.10.3: `∫₀^∞ x^{s-1} (1 - θ₄(0|ix²)) dx = (1 - 2^{1-s}) π^{-s/2} Γ(s/2) ζ(s)`,
`Re s > 0`, `s ≠ 1` (see `mellin_one_sub_jacobiThetaFourNullTau_one` for `s = 1`).
Corrected from the printed DLMF formula: `s = 1` is excluded because there the right side is a
removable singularity, whereas Lean's totalized `riemannZeta 1` would make it `0` instead of
the limit `ln 2`. -/
@[dlmf 20.10.E3]
theorem mellin_one_sub_jacobiThetaFourNullTau {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * (1 - jacobiThetaFourNullTau (I * x ^ 2)))
        (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * (1 - jacobiThetaFourNullTau (I * x ^ 2)) =
        (1 - 2 ^ (1 - s)) * (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s := by
  sorry

/-- DLMF 20.10.3 at the removable point `s = 1`: `∫₀^∞ (1 - θ₄(0|ix²)) dx = ln 2`.
Corrected from the printed DLMF formula: the printed right side `(1 - 2^{1-s}) π^{-s/2} Γ(s/2) ζ(s)`
is `0 · ∞` at `s = 1`; its limit `ln 2` is stated explicitly (checked with mpmath). -/
@[dlmf 20.10.E3 "removable point s = 1 of the right side"]
theorem mellin_one_sub_jacobiThetaFourNullTau_one :
    IntegrableOn (fun x : ℝ => 1 - jacobiThetaFourNullTau (I * x ^ 2)) (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), (1 - jacobiThetaFourNullTau (I * x ^ 2)) = Real.log 2 := by
  sorry

/-- DLMF 20.10.4: for `Re s > 0`, `ℓ > 0`, `|Re β| + |Im β| ≤ ℓ`,
`∫₀^∞ e^{-st} θ₁(βπ/(2ℓ)|iπt/ℓ²) dt = -∫₀^∞ e^{-st} θ₂((ℓ+β)π/(2ℓ)|iπt/ℓ²) dt
  = (ℓ/√s) sinh(β√s) sech(ℓ√s)`. -/
@[dlmf 20.10.E4]
theorem laplace_jacobiThetaOneTau {s β : ℂ} {ℓ : ℝ} (hs : 0 < s.re) (hℓ : 0 < ℓ)
    (hβ : |β.re| + |β.im| ≤ ℓ) :
    IntegrableOn (fun t : ℝ => cexp (-s * t) *
        jacobiThetaOneTau (β * π / (2 * ℓ)) (I * π * t / ℓ ^ 2))
        (Set.Ioi 0) ∧
      IntegrableOn (fun t : ℝ => cexp (-s * t) *
        jacobiThetaTwoTau ((ℓ + β) * π / (2 * ℓ)) (I * π * t / ℓ ^ 2)) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), cexp (-s * t) *
          jacobiThetaOneTau (β * π / (2 * ℓ)) (I * π * t / ℓ ^ 2) =
        ℓ / s ^ (1 / 2 : ℂ) * sinh (β * s ^ (1 / 2 : ℂ)) / cosh (ℓ * s ^ (1 / 2 : ℂ)) ∧
      -∫ t in Set.Ioi (0 : ℝ), cexp (-s * t) *
          jacobiThetaTwoTau ((ℓ + β) * π / (2 * ℓ)) (I * π * t / ℓ ^ 2) =
        ℓ / s ^ (1 / 2 : ℂ) * sinh (β * s ^ (1 / 2 : ℂ)) / cosh (ℓ * s ^ (1 / 2 : ℂ)) := by
  sorry

/-- DLMF 20.10.5: for `Re s > 0`, `ℓ > 0`, `|Re β| + |Im β| ≤ ℓ`,
`∫₀^∞ e^{-st} θ₃((ℓ+β)π/(2ℓ)|iπt/ℓ²) dt = ∫₀^∞ e^{-st} θ₄(βπ/(2ℓ)|iπt/ℓ²) dt
  = (ℓ/√s) cosh(β√s) csch(ℓ√s)`. -/
@[dlmf 20.10.E5]
theorem laplace_jacobiThetaThreeTau {s β : ℂ} {ℓ : ℝ} (hs : 0 < s.re) (hℓ : 0 < ℓ)
    (hβ : |β.re| + |β.im| ≤ ℓ) :
    IntegrableOn (fun t : ℝ => cexp (-s * t) *
        jacobiThetaThreeTau ((ℓ + β) * π / (2 * ℓ)) (I * π * t / ℓ ^ 2)) (Set.Ioi 0) ∧
      IntegrableOn (fun t : ℝ => cexp (-s * t) *
        jacobiThetaFourTau (β * π / (2 * ℓ)) (I * π * t / ℓ ^ 2)) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), cexp (-s * t) *
          jacobiThetaThreeTau ((ℓ + β) * π / (2 * ℓ)) (I * π * t / ℓ ^ 2) =
        ℓ / s ^ (1 / 2 : ℂ) * cosh (β * s ^ (1 / 2 : ℂ)) / sinh (ℓ * s ^ (1 / 2 : ℂ)) ∧
      ∫ t in Set.Ioi (0 : ℝ), cexp (-s * t) *
          jacobiThetaFourTau (β * π / (2 * ℓ)) (I * π * t / ℓ ^ 2) =
        ℓ / s ^ (1 / 2 : ℂ) * cosh (β * s ^ (1 / 2 : ℂ)) / sinh (ℓ * s ^ (1 / 2 : ℂ)) := by
  sorry

end DLMF.Theta

end
