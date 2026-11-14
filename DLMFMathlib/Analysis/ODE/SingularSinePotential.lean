/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.GeneralWeightedVolterra
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Sine-kernel estimates at an integrably singular initial endpoint

Olver, *Asymptotics and Special Functions*, Chapter 6, Theorem 7.1 and
§7.2, pp. 209–210, synopsis O-6.09. The potential need not be bounded
at zero; its actual sine-majorant weighted integral is the hypothesis.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Asymptotics
open scoped Topology Real

namespace Real

/-- The running maximum of the absolute sine on `[0,max(x,0)]`.
Olver, Chapter 6, §7.1, synopsis O-6.09. -/
def sineMajorant (x : ℝ) : ℝ := sSup ((fun t : ℝ => |sin t|) '' Icc 0 (max x 0))

/-- The defining compact-interval maximum. -/
theorem sineMajorant_def (x : ℝ) :
    sineMajorant x = sSup ((fun t : ℝ => |sin t|) '' Icc 0 (max x 0)) := rfl

/-- The explicit sine majorant, including its saturation at the first sine maximum.
Olver, §7.1, synopsis O-6.09. -/
theorem sineMajorant_eq (x : ℝ) (hx : 0 ≤ x) :
    sineMajorant x = if x ≤ π / 2 then sin x else 1 := by
  sorry

end Real

namespace ODE.SingularSinePotential

/-- The actual weighted error-control integral from the singular endpoint.
Olver, Theorem 7.1, synopsis O-6.09. -/
def control (g : ℝ → ℂ) (u x : ℝ) : ℝ :=
  u⁻¹ * ∫ t : ℝ in Ioc 0 x, Real.sineMajorant (u * t) * ‖g t‖

/-- The defining control integral. -/
theorem control_def (g : ℝ → ℂ) (u x : ℝ) :
    control g u x = u⁻¹ * ∫ t : ℝ in Ioc 0 x, Real.sineMajorant (u * t) * ‖g t‖ := rfl

/-- A potential with finite weighted integral gives a normalized solution through zero,
the actual Volterra equation, and the sharp sine-majorant error bound.
Olver, Chapter 6, Theorem 7.1, synopsis O-6.09. -/
theorem exists_solution {b : EReal} (hb : 0 < b) {u : ℝ} (hu : 0 < u)
    {g : ℝ → ℂ} (hg : ContinuousOn g (ODE.WeightedVolterra.interval 0 b))
    (hint : ∀ x ∈ ODE.WeightedVolterra.interval 0 b,
      IntegrableOn (fun t => Real.sineMajorant (u * t) * ‖g t‖) (Ioc 0 x)) :
    ∃ w : ℝ → ℂ,
      ContDiffOn ℝ 1 w {x | 0 ≤ x ∧ (x : EReal) < b} ∧
      ContDiffOn ℝ 2 w (ODE.WeightedVolterra.interval 0 b) ∧
      w 0 = 0 ∧ HasDerivWithinAt w (u : ℂ) (Ici 0) 0 ∧
      (∀ x ∈ ODE.WeightedVolterra.interval 0 b,
        deriv (deriv w) x = (-(u : ℂ) ^ 2 + g x) * w x ∧
        w x - Real.sin (u * x) =
          (u : ℂ)⁻¹ * ∫ t : ℝ in Ioc 0 x,
            (Real.sin (u * (x - t)) : ℂ) * g t * w t ∧
        ‖w x - Real.sin (u * x)‖ ≤ Real.sineMajorant (u * x) *
          (Real.exp (control g u x) - 1)) := by
  sorry

/-- A `1/x`-bounded real potential near zero and an integrable tail give uniform
high-frequency sine error and small real scattering amplitude and phase corrections.
The normalizer is the singular-end initial derivative, not an arbitrary solution scale.
Olver, Chapter 6, §7.2, synopsis O-6.09. -/
theorem exists_scattering_family {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ioi 0))
    (hzero : g =O[𝓝[>] (0 : ℝ)] fun x => x⁻¹)
    (htail : IntegrableOn g (Ici 1)) :
    ∃ (w : ℝ → ℝ → ℝ) (amplitude phase : ℝ → ℝ) (C u₀ : ℝ),
      0 < C ∧ 1 < u₀ ∧
      (∀ u, 0 < u →
        ContDiffOn ℝ 1 (w u) (Ici 0) ∧ ContDiffOn ℝ 2 (w u) (Ioi 0) ∧
        w u 0 = 0 ∧ HasDerivWithinAt (w u) u (Ici 0) 0 ∧
        (∀ x > 0, deriv (deriv (w u)) x = (-u ^ 2 + g x) * w u x) ∧
        0 < amplitude u ∧
        Tendsto (fun x => w u x - amplitude u * Real.sin (u * x + phase u))
          atTop (𝓝 0)) ∧
      (∀ u ≥ u₀,
        |amplitude u - 1| ≤ C * Real.log u / u ∧
        |phase u| ≤ C * Real.log u / u ∧
        ∀ x ≥ 0, |w u x - Real.sin (u * x)| ≤
          Real.sineMajorant (u * x) * C * Real.log u / u) := by
  sorry

end ODE.SingularSinePotential
