/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Debye
public import DLMF.Bessel.LogarithmicMonodromy
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import Mathlib.Analysis.BoundedVariation

/-!
# Debye errors on the logarithmic cover

The lifted phase has the actual logarithm coordinate as its linear term.
The `I` remainder includes its finite-truncation origin normalization, whose
infinity multiplier can vanish at small orders. The cleared identity is retained
at those exceptional values. Source: Olver, *Asymptotics and Special Functions*,
Chapter 10, (7.12)–(7.17) and §8, pp. 376–382.
-/

@[expose] public noncomputable section

open Complex Set Filter Finset
open scoped Real Topology

namespace DLMF.Bessel.Debye

/-- The logarithmic lift of the plane cut along the two outer imaginary rays.
The turning points themselves are excluded. Olver, Chapter 10, §8, pp. 378–382. -/
def liftDomain : Set ℂ := {w | 1 + exp (2 * w) ∈ slitPlane}

/-- The lifted domain retains the principal square root of `1+z^2`. -/
theorem mem_liftDomain_iff (w : ℂ) : w ∈ liftDomain ↔ 1 + exp (2 * w) ∈ slitPlane :=
  Iff.rfl

/-- The Debye phase on the logarithmic cover, continued from positive arguments.
Olver, Chapter 10, (7.07), p. 375, and §8. -/
def phaseOnLog (w : ℂ) : ℂ :=
  sqrt (1 + exp (2 * w)) + w - log (1 + sqrt (1 + exp (2 * w)))

/-- The defining lifted phase. -/
theorem phaseOnLog_def (w : ℂ) : phaseOnLog w =
    sqrt (1 + exp (2 * w)) + w - log (1 + sqrt (1 + exp (2 * w))) := rfl

/-- The exact normalized origin value, equal to the reciprocal scaled Gamma
factor for positive real order. Olver, Chapter 10, §7.4, p. 377. -/
def originFactor (ν : ℂ) : ℂ :=
  (2 * Real.pi * ν) ^ (1 / 2 : ℂ) * exp (ν * (log ν - 1)) / Gamma (ν + 1)

/-- The defining Gamma normalization at the origin. -/
theorem originFactor_def (ν : ℂ) : originFactor ν =
    (2 * Real.pi * ν) ^ (1 / 2 : ℂ) * exp (ν * (log ν - 1)) / Gamma (ν + 1) := rfl

/-- The finite Debye coefficient sum, alternating for `K`.
Olver, Chapter 10, (7.12)–(7.13), p. 377. -/
def coefficientSum (k : Fin 2) (ν : ℂ) (n : ℕ) (t : ℂ) : ℂ :=
  ∑ s ∈ range n, (if k = 0 then 1 else (-1 : ℂ) ^ s) * coefficientU s t / ν ^ s

/-- The defining finite Debye coefficient sum. -/
theorem coefficientSum_def (k : Fin 2) (ν : ℂ) (n : ℕ) (t : ℂ) :
    coefficientSum k ν n t =
      ∑ s ∈ range n, (if k = 0 then 1 else (-1 : ℂ) ^ s) * coefficientU s t / ν ^ s := rfl

/-- The normalized lifted `I` or `K`, with its dominant exponential removed.
Olver, Chapter 10, (7.16)–(7.17), p. 377. -/
def normalizedFunction (k : Fin 2) (ν w : ℂ) : ℂ :=
  let q := (1 + exp (2 * w)) ^ (1 / 4 : ℂ)
  if k = 0 then
    (2 * Real.pi * ν) ^ (1 / 2 : ℂ) * q * exp (-ν * phaseOnLog w) *
      besselIOnLog ν (log ν + w)
  else
    (2 * ν / Real.pi) ^ (1 / 2 : ℂ) * q * exp (ν * phaseOnLog w) *
      besselKOnLog ν (log ν + w)

/-- The defining lifted normalized Bessel functions. -/
theorem normalizedFunction_def (k : Fin 2) (ν w : ℂ) : normalizedFunction k ν w =
    let q := (1 + exp (2 * w)) ^ (1 / 4 : ℂ)
    if k = 0 then
      (2 * Real.pi * ν) ^ (1 / 2 : ℂ) * q * exp (-ν * phaseOnLog w) *
        besselIOnLog ν (log ν + w)
    else
      (2 * ν / Real.pi) ^ (1 / 2 : ℂ) * q * exp (ν * phaseOnLog w) *
        besselKOnLog ν (log ν + w) := rfl

/-- The actual finite-truncation remainder; `I` retains its origin multiplier.
Olver, Chapter 10, (7.14)–(7.17), p. 377. -/
def remainder (k : Fin 2) (ν : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  (if k = 0 then coefficientSum 0 ν n 1 / originFactor ν else 1) *
      normalizedFunction k ν w -
    coefficientSum k ν n ((sqrt (1 + exp (2 * w)))⁻¹)

/-- The defining actual Debye remainder, including the finite origin factor. -/
theorem remainder_def (k : Fin 2) (ν : ℂ) (n : ℕ) (w : ℂ) : remainder k ν n w =
    (if k = 0 then coefficientSum 0 ν n 1 / originFactor ν else 1) *
        normalizedFunction k ν w -
      coefficientSum k ν n ((sqrt (1 + exp (2 * w)))⁻¹) := rfl

/-- The exact cleared `I` normalization is valid even when the finite origin
sum vanishes. Division by that sum requires its explicit nonvanishing.
Olver, Chapter 10, (7.16), p. 377. -/
theorem normalizedFunction_I_cleared (ν w : ℂ) (n : ℕ) (hν : originFactor ν ≠ 0) :
    coefficientSum 0 ν n 1 * normalizedFunction 0 ν w =
      originFactor ν * (coefficientSum 0 ν n ((sqrt (1 + exp (2 * w)))⁻¹) +
        remainder 0 ν n w) := by
  rw [remainder_def, if_pos rfl]
  field_simp [hν]
  ring

/-- The origin and infinity factors match the canonical Bessel normalizations.
Olver, Chapter 10, §7.4, p. 377. -/
theorem normalizedFunction_limits {ν : ℂ} (hν : 0 < ν.re) :
    originFactor ν ≠ 0 ∧
      Tendsto (fun t : ℝ => normalizedFunction 0 ν t) atBot (𝓝 (originFactor ν)) ∧
      ∀ k : Fin 2, Tendsto (fun t : ℝ => normalizedFunction k ν t) atTop (𝓝 1) := by
  sorry

/-- The full `I` variation bound on any lifted progressive path from the origin.
The real part of `nu*eta` is the actual complex-order progressivity predicate.
Olver, Chapter 10, (7.14), §8.1 and §8.4, pp. 377–382. -/
theorem norm_remainder_I_le {ν : ℂ} (hν : 0 < ν.re) {n : ℕ} (hn : 0 < n)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ioc 0 1))
    (hregular : ∀ a : ℝ, 0 < a → a < 1 → TauCeti.IsPiecewiseC1On γ a 1)
    (himage : γ '' Ioc 0 1 ⊆ liftDomain)
    (horigin : Tendsto (fun t => (γ t).re) (𝓝[>] 0) atBot)
    (hargument : ∃ b : ℝ, Tendsto (fun t => (γ t).im) (𝓝[>] 0) (𝓝 b))
    (hprogressive : MonotoneOn (fun t => (ν * phaseOnLog (γ t)).re) (Ioc 0 1))
    (hvariation : ∀ s ∈ ({1, n} : Set ℕ), BoundedVariationOn
      (fun t => coefficientU s ((sqrt (1 + exp (2 * γ t)))⁻¹)) (Ioc 0 1)) :
    let V := fun s => (eVariationOn
      (fun t => coefficientU s ((sqrt (1 + exp (2 * γ t)))⁻¹)) (Ioc 0 1)).toReal
    ‖remainder 0 ν n (γ 1)‖ ≤ 2 * Real.exp (2 * V 1 / ‖ν‖) * V n / ‖ν‖ ^ n := by
  sorry

/-- The full `K` variation bound on lifted paths from its canonical infinity
reference. Changing the reference sheet selects a different recessive solution;
the chosen tail here approaches the positive real argument sheet.
Olver, Chapter 10, (7.15), §8.2–§8.4, pp. 377–382. -/
theorem norm_remainder_K_le {ν : ℂ} (hν : 0 < ν.re) {n : ℕ} (hn : 0 < n)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ioc 0 1))
    (hregular : ∀ a : ℝ, 0 < a → a < 1 → TauCeti.IsPiecewiseC1On γ a 1)
    (himage : γ '' Ioc 0 1 ⊆ liftDomain)
    (hinfinity : Tendsto (fun t => (γ t).re) (𝓝[>] 0) atTop)
    (hargument : Tendsto (fun t => (γ t).im) (𝓝[>] 0) (𝓝 0))
    (hprogressive : AntitoneOn (fun t => (ν * phaseOnLog (γ t)).re) (Ioc 0 1))
    (hvariation : ∀ s ∈ ({1, n} : Set ℕ), BoundedVariationOn
      (fun t => coefficientU s ((sqrt (1 + exp (2 * γ t)))⁻¹)) (Ioc 0 1)) :
    let V := fun s => (eVariationOn
      (fun t => coefficientU s ((sqrt (1 + exp (2 * γ t)))⁻¹)) (Ioc 0 1)).toReal
    ‖remainder 1 ν n (γ 1)‖ ≤ 2 * Real.exp (2 * V 1 / ‖ν‖) * V n / ‖ν‖ ^ n := by
  sorry

end DLMF.Bessel.Debye
