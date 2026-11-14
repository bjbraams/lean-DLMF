/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Amplitude and phase bounds from a relative complex error

Olver, *Asymptotics and Special Functions*, Chapter 13, §14,
pp. 510–513, synopsis O-13.11. The disc centered at one yields a sharp
arcsine angle bound, including the zero-amplitude endpoint.
-/

@[expose] public noncomputable section
namespace Complex

/-- A relative error of norm at most one gives the source's amplitude and phase
bounds. Olver, Chapter 13, §14, pp. 510–513. If 1+epsilon=0, choose zero phase. -/
theorem exists_amplitude_phase_error {ε : ℂ} (hε : ‖ε‖ ≤ 1) :
    ∃ p q : ℝ, 0 ≤ 1 + p ∧
      1 + ε = (1 + p : ℝ) * exp (-I * q) ∧ |p| ≤ ‖ε‖ ∧
        |q| ≤ Real.arcsin ‖ε‖ ∧ Real.arcsin ‖ε‖ ≤ Real.pi * ‖ε‖ / 2 := by
  sorry

end Complex
