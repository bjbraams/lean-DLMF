/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# All-order smooth stationary phase in a Morse coordinate

Olver, *Asymptotics and Special Functions*, Chapter 3, §14, pp. 103–104,
synopsis O-3.16. The coefficient amplitude is the actual pullback `q(h(u))h'(u)`;
the finite-interval form explicitly includes both nonstationary endpoint series.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory Complex Asymptotics Finset
open scoped Topology ContDiff

namespace Asymptotics

/-- All-order stationary phase for a smooth compactly supported amplitude, in an actual
orientation-preserving Morse coordinate. Olver, Chapter 3, §14, synopsis O-3.16. -/
theorem hasAsymptoticExpansion_stationaryPhase_morse
    {p : ℝ → ℝ} {q : ℝ → ℂ} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (hcompact : HasCompactSupport q) {t₀ δ σ : ℝ} (hδ : 0 < δ)
    (hσ : σ = 1 ∨ σ = -1) (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ ∞ h (Ioo (-δ) δ)) (hzero : h 0 = t₀)
    (hpositive : 0 < deriv h 0)
    (hphase : ∀ u ∈ Ioo (-δ) δ, p (h u) = p t₀ + σ * u ^ 2 / 2)
    (hregular : ∀ t ∈ tsupport q, t ≠ t₀ → deriv p t ≠ 0) :
    HasAsymptoticExpansion atTop
      (fun n (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + 1 / 2)))
      (fun n => exp (I * σ * Real.pi / 4) * Real.sqrt (2 * Real.pi) *
        (I * σ) ^ n * iteratedDeriv (2 * n)
          (fun u => q (h u) * ((deriv h u : ℝ) : ℂ)) 0 / (2 ^ n * (n.factorial : ℂ)))
      (fun x => ∫ t : ℝ, exp (I * x * (p t - p t₀)) * q t) := by
  sorry

/-- The finite-endpoint all-order expansion combines the stationary contribution with the
explicit endpoint series. Olver, Chapter 3, §14, synopsis O-3.16. The derivative operator
in the endpoint coefficients is iterated on the actual amplitude. -/
theorem isBigO_stationaryPhase_morse_sub_sums
    {a b t₀ δ σ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hδ : 0 < δ)
    {p : ℝ → ℝ} {q : ℝ → ℂ} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (hσ : σ = 1 ∨ σ = -1) (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ ∞ h (Ioo (-δ) δ)) (hzero : h 0 = t₀)
    (hpositive : 0 < deriv h 0) (himage : MapsTo h (Ioo (-δ) δ) (Ioo a b))
    (hphase : ∀ u ∈ Ioo (-δ) δ, p (h u) = p t₀ + σ * u ^ 2 / 2)
    (hregular : ∀ t ∈ Icc a b, t ≠ t₀ → deriv p t ≠ 0) (N : ℕ) :
    let D : ℕ → ℝ → ℂ := fun k =>
      (fun f : ℝ → ℂ => deriv (fun t => f t / ((deriv p t : ℝ) : ℂ)))^[k] q
    (fun x : ℝ => (∫ t in a..b, exp (I * x * (p t - p t₀)) * q t) -
      exp (I * σ * Real.pi / 4) * Real.sqrt (2 * Real.pi) *
        ∑ n ∈ range N, (I * σ) ^ n * iteratedDeriv (2 * n)
          (fun u => q (h u) * ((deriv h u : ℝ) : ℂ)) 0 /
          (2 ^ n * (n.factorial : ℂ)) * (x : ℂ) ^ (-((n : ℂ) + 1 / 2)) -
      ∑ k ∈ range (N + 1), (-1 : ℂ) ^ k / (I * x) ^ (k + 1) *
        (exp (I * x * (p b - p t₀)) * D k b / ((deriv p b : ℝ) : ℂ) -
          exp (I * x * (p a - p t₀)) * D k a / ((deriv p a : ℝ) : ℂ)))
        =O[atTop] (fun x : ℝ => x ^ (-((N : ℝ) + 1 / 2))) := by
  sorry

end Asymptotics
