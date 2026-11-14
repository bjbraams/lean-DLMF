/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Integrated inverse-power expansions with their integration constant

Olver, *Asymptotics and Special Functions*, Chapter 1, §8.2, pp. 20–21,
synopsis O-1.14. The inverse-linear coefficient contributes a logarithm.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory Asymptotics Finset
open scoped Topology

namespace Asymptotics

/-- Termwise indefinite integration preserves a full expansion after adding its uniquely
specified integration constant and logarithmic term. Olver, Chapter 1, §8.2, synopsis O-1.14. -/
theorem HasAsymptoticExpansion.exists_intervalIntegral_inv_pow {f : ℝ → ℂ}
    {a : ℕ → ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hi : ∀ b, x₀ ≤ b → IntervalIntegrable f volume x₀ b)
    (hf : HasAsymptoticExpansion atTop (fun n (x : ℝ) => x⁻¹ ^ n) a f) :
    ∃ C : ℂ, ∀ N : ℕ,
      (fun x : ℝ => (∫ t in x₀..x, f t) -
        (a 0 * x + a 1 * Real.log x + C -
          ∑ k ∈ Icc 2 (N + 1), a k / (k - 1 : ℂ) * (x : ℂ)⁻¹ ^ (k - 1)))
        =O[atTop] (fun x : ℝ => x⁻¹ ^ (N + 1)) := by
  sorry

end Asymptotics
