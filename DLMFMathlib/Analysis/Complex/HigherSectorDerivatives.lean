/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.Sector
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Arbitrary-order derivative bounds inside sectors

Olver, *Asymptotics and Special Functions*, Chapter 1, Theorem 4.2, pp. 9–10,
synopsis O-1.06. The circle radius is an explicit positive multiple of `|z|`;
this gives a Cauchy constant independent of the radial cutoff and function.
-/

@[expose] public noncomputable section

open Filter

namespace Complex

/-- Explicit arbitrary-order Cauchy estimate inside a properly smaller rotated sector.
Olver, Chapter 1, Theorem 4.2, pp. 9–10, synopsis O-1.06. The radius factor is
half the sine of the angular margin, capped at a right angle. -/
theorem norm_iteratedDeriv_le_of_sector_bound {ω η : ℝ}
    (hη : 0 ≤ η) (hηω : η < ω) (hω : ω ≤ Real.pi)
    (θ p R B : ℝ) (hB : 0 ≤ B) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f
      {z | R < ‖z‖ ∧ |arg (z * exp (-(θ * I)))| < ω})
    (hbound : ∀ z : ℂ, R < ‖z‖ → |arg (z * exp (-(θ * I)))| < ω →
      ‖f z‖ ≤ B * ‖z‖ ^ p) (m : ℕ) {z : ℂ}
    (hz : 2 * max R 0 < ‖z‖) (harg : |arg (z * exp (-(θ * I)))| ≤ η) :
    let c := Real.sin (min (ω - η) (Real.pi / 2)) / 2
    ‖iteratedDeriv m f z‖ ≤
      (m.factorial : ℝ) * (2 : ℝ) ^ |p| / c ^ m * B * ‖z‖ ^ (p - m) := by
  sorry

/-- Uniform sectorial big-oh estimates differentiate to every fixed order on a properly
interior sector. Olver, Chapter 1, Theorem 4.2, pp. 9–10, synopsis O-1.06. -/
theorem isBigO_iteratedDeriv_of_sector {ω η : ℝ}
    (hη : 0 ≤ η) (hηω : η < ω) (hω : ω ≤ Real.pi) (θ p R : ℝ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f
      {z | R < ‖z‖ ∧ |arg (z * exp (-(θ * I)))| < ω})
    (hbound : f =O[comap (fun z : ℂ => ‖z‖) atTop ⊓
      𝓟 {z | |arg (z * exp (-(θ * I)))| < ω}] (fun z => ‖z‖ ^ p)) (m : ℕ) :
    iteratedDeriv m f =O[comap (fun z : ℂ => ‖z‖) atTop ⊓
      𝓟 {z | |arg (z * exp (-(θ * I)))| ≤ η}] (fun z => ‖z‖ ^ (p - m)) := by
  sorry

/-- Uniform sectorial little-oh estimates differentiate to every fixed order on a properly
interior sector. Olver, Chapter 1, Theorem 4.2, pp. 9–10, synopsis O-1.06. -/
theorem isLittleO_iteratedDeriv_of_sector {ω η : ℝ}
    (hη : 0 ≤ η) (hηω : η < ω) (hω : ω ≤ Real.pi) (θ p R : ℝ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f
      {z | R < ‖z‖ ∧ |arg (z * exp (-(θ * I)))| < ω})
    (hbound : f =o[comap (fun z : ℂ => ‖z‖) atTop ⊓
      𝓟 {z | |arg (z * exp (-(θ * I)))| < ω}] (fun z => ‖z‖ ^ p)) (m : ℕ) :
    iteratedDeriv m f =o[comap (fun z : ℂ => ‖z‖) atTop ⊓
      𝓟 {z | |arg (z * exp (-(θ * I)))| ≤ η}] (fun z => ‖z‖ ^ (p - m)) := by
  sorry

end Complex
