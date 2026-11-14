/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Integral.RepeatedIntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact Laplace integration-by-parts remainders

Olver, *Asymptotics and Special Functions*, Chapter 3, §§1–2, pp. 66–70,
synopsis O-3.01. Finite upper-endpoint terms are retained before taking a limit.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex Filter Finset
open scoped Topology

namespace intervalIntegral

/-- The exact finite-interval Laplace boundary expansion, with no discarded endpoint.
Olver, Chapter 3, §§1–2, synopsis O-3.01. -/
theorem integral_exp_neg_mul_eq_sum_add {b x : ℝ} (hb : 0 ≤ b) (hx : 0 < x)
    (D : ℕ → ℝ → ℂ) (N : ℕ)
    (hD : ∀ k ≤ N, ContinuousOn (D k) (Icc 0 b))
    (hd : ∀ k < N, ∀ t ∈ Icc 0 b,
      HasDerivWithinAt (D k) (D (k + 1) t) (Icc 0 b) t) :
    (∫ t in (0 : ℝ)..b, exp (-x * t) * D 0 t) =
      ∑ k ∈ range N, (D k 0 - exp (-x * b) * D k b) / (x : ℂ) ^ (k + 1) +
        (x : ℂ)⁻¹ ^ N * ∫ t in (0 : ℝ)..b, exp (-x * t) * D N t := by
  sorry

/-- The half-line formula is an ordinary improper limit, allowing a conditional final remainder.
Olver, Chapter 3, §§1–2, synopsis O-3.01. -/
theorem tendsto_integral_exp_neg_mul_of_derivatives {x : ℝ} (hx : 0 < x)
    (D : ℕ → ℝ → ℂ) (N : ℕ)
    (hD : ∀ k ≤ N, ContinuousOn (D k) (Set.Ici 0))
    (hd : ∀ k < N, ∀ t ∈ Set.Ici 0,
      HasDerivWithinAt (D k) (D (k + 1) t) (Set.Ici 0) t)
    (hend : ∀ k < N, Tendsto (fun b : ℝ => exp (-x * b) * D k b) atTop (𝓝 0))
    {L : ℂ} (hrem : Tendsto (fun b : ℝ =>
      ∫ t in (0 : ℝ)..b, exp (-x * t) * D N t) atTop (𝓝 L)) :
    Tendsto (fun b : ℝ => ∫ t in (0 : ℝ)..b, exp (-x * t) * D 0 t) atTop
      (𝓝 (∑ k ∈ range N, D k 0 / (x : ℂ) ^ (k + 1) + (x : ℂ)⁻¹ ^ N * L)) := by
  sorry

end intervalIntegral
