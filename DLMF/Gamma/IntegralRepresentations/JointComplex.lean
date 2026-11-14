/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Joint complex integrals for digamma and logarithmic gamma

Andrews, Askey and Roy, *Special Functions*, Theorems 1.6.1–1.6.3.
The logarithmic gamma is TauCeti's analytic branch on the slit plane, real on
the positive real axis. Singular summands at zero are integrated together.
Each evaluation includes integrability of the combined integrand.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace DLMF.Gamma

/-- The algebraic-kernel joint integral for digamma in the right half-plane.
Andrews–Askey–Roy, *Special Functions*, Theorem 1.6.1, p. 26
(synopsis AAR-1.6.1–1.7.1); Temme, *Special Functions*, §3.8. -/
theorem digamma_integral_algebraic {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ =>
      (exp (-(t : ℂ)) - (1 + (t : ℂ)) ^ (-z)) / (t : ℂ)) (Ioi 0) ∧
      digamma z = ∫ t : ℝ in Ioi 0,
        (exp (-(t : ℂ)) - (1 + (t : ℂ)) ^ (-z)) / (t : ℂ) := by
  sorry

/-- The exponential-kernel joint integral for digamma in the right half-plane.
Andrews–Askey–Roy, *Special Functions*, Theorem 1.6.1, p. 26
(synopsis AAR-1.6.1–1.7.1); Temme, *Special Functions*, §3.8. -/
theorem digamma_integral_exponential {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => exp (-(t : ℂ)) / (t : ℂ) -
      exp (-z * t) / (1 - exp (-(t : ℂ)))) (Ioi 0) ∧
      digamma z = ∫ t : ℝ in Ioi 0,
        exp (-(t : ℂ)) / (t : ℂ) - exp (-z * t) / (1 - exp (-(t : ℂ))) := by
  sorry

/-- Malmsten's joint integral for the analytic logarithmic gamma.
Andrews–Askey–Roy, *Special Functions*, Theorem 1.6.2, p. 27
(synopsis AAR-1.6.1–1.7.1); Temme, *Special Functions*, §3.8. -/
theorem logGamma_integral_malmsten {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => ((z - 1) * exp (-(t : ℂ)) -
      (exp (-(t : ℂ)) - exp (-z * t)) / (1 - exp (-(t : ℂ)))) / (t : ℂ)) (Ioi 0) ∧
      TauCeti.logGamma z = ∫ t : ℝ in Ioi 0,
        ((z - 1) * exp (-(t : ℂ)) -
          (exp (-(t : ℂ)) - exp (-z * t)) / (1 - exp (-(t : ℂ)))) / (t : ℂ) := by
  sorry

/-- Binet's exponential integral for analytic logarithmic gamma on the right half-plane.
Andrews–Askey–Roy, *Special Functions*, Theorem 1.6.3, p. 28
(synopsis AAR-1.6.1–1.7.1); Temme, *Special Functions*, §3.8. -/
theorem logGamma_integral_binet_exponential {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (1 / 2 - 1 / (t : ℂ) + 1 / (exp (t : ℂ) - 1)) *
      exp (-z * t) / (t : ℂ)) (Ioi 0) ∧
      TauCeti.logGamma z = (z - 1 / 2) * log z - z + log (2 * Real.pi : ℂ) / 2 +
        ∫ t : ℝ in Ioi 0,
          (1 / 2 - 1 / (t : ℂ) + 1 / (exp (t : ℂ) - 1)) * exp (-z * t) / (t : ℂ) := by
  sorry

/-- Binet's arctangent integral, on the analytic arctangent branch continued from positive
real arguments. Andrews–Askey–Roy, *Special Functions*, Theorem 1.6.3, p. 28
(synopsis AAR-1.6.1–1.7.1); Temme, *Special Functions*, §3.8. -/
theorem logGamma_integral_binet_arctan {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => arctan ((t : ℂ) / z) /
      (exp (2 * Real.pi * t : ℂ) - 1)) (Ioi 0) ∧
      TauCeti.logGamma z = (z - 1 / 2) * log z - z + log (2 * Real.pi : ℂ) / 2 +
        2 * ∫ t : ℝ in Ioi 0, arctan ((t : ℂ) / z) /
          (exp (2 * Real.pi * t : ℂ) - 1) := by
  sorry

end DLMF.Gamma
