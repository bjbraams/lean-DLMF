/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Basic
public import DLMF.Airy.Basic.Scorer
public import DLMFMathlib.Analysis.Asymptotics.PerturbedLaplace
public import Mathlib.Analysis.Analytic.Basic

/-!
# Faxen's integral

The entire function of its last variable defined by
`Fi(a,b;y) = integral exp(-t + y*t^a)*t^(b-1)` for `0 <= re a < 1`, `0 < re b`.
The powers of positive real `t` use its real logarithm. This is Olver,
*Asymptotics and Special Functions*, Chapter 9, §4, pp. 332–333; its role as the
critical perturbed-Laplace coefficient is formalized in `PerturbedLaplace`.
-/

@[expose] public noncomputable section

open Set MeasureTheory Complex

namespace DLMF.AsymptoticApproximations

/-- Faxen's integral on the positive real axis, with `t^a = exp(a*log(t))`.
The integral is absolutely convergent for `0 <= re a < 1` and `0 < re b`; outside
that parameter domain this definition uses Lean's totalized integral. Olver,
Chapter 9, §4, p. 332. -/
def faxenIntegral (a b y : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), exp (-(t : ℂ) + y * (t : ℂ) ^ a) * (t : ℂ) ^ (b - 1)

/-- The defining positive-axis integral of the Faxen function. -/
theorem faxenIntegral_def (a b y : ℂ) :
    faxenIntegral a b y =
      ∫ t in Ioi (0 : ℝ), exp (-(t : ℂ) + y * (t : ℂ) ^ a) * (t : ℂ) ^ (b - 1) := rfl

/-- Absolute convergence of Faxen's integral throughout its source parameter domain.
Olver, Chapter 9, §4, p. 332. -/
theorem integrableOn_faxenIntegral {a b : ℂ} (ha : 0 ≤ a.re) (ha' : a.re < 1)
    (hb : 0 < b.re) (y : ℂ) :
    IntegrableOn (fun t : ℝ =>
      exp (-(t : ℂ) + y * (t : ℂ) ^ a) * (t : ℂ) ^ (b - 1)) (Ioi 0) := by
  sorry

/-- Faxen's integral is entire in `y`. Olver, Chapter 9, §4, p. 332. -/
theorem analyticOnNhd_faxenIntegral {a b : ℂ} (ha : 0 ≤ a.re) (ha' : a.re < 1)
    (hb : 0 < b.re) : AnalyticOnNhd ℂ (faxenIntegral a b) univ := by
  sorry

/-- The Taylor coefficients of Faxen's integral are Gamma values obtained by
integrating the exponential series. Olver, Chapter 9, §4, p. 332. -/
theorem hasSum_faxenIntegral {a b : ℂ} (ha : 0 ≤ a.re) (ha' : a.re < 1)
    (hb : 0 < b.re) (y : ℂ) :
    HasSum (fun n : ℕ => Gamma (b + a * n) * y ^ n / n.factorial)
      (faxenIntegral a b y) := by
  sorry

/-- At `a=b=1/2` Faxen's function is an error-function expression, with the
normalization continued from the positive real axis. Olver, Chapter 9, §4, p. 332. -/
theorem faxenIntegral_half_half (y : ℂ) :
    faxenIntegral (1 / 2) (1 / 2) y =
      Real.sqrt Real.pi * exp (y ^ 2 / 4) * (1 + DLMF.Confluent.erf (y / 2)) := by
  sorry

/-- At `a=b=1/3` Faxen's function is Scorer's `Hi`. Olver, Chapter 9, §4, p. 332. -/
theorem faxenIntegral_third_third (y : ℂ) :
    faxenIntegral (1 / 3) (1 / 3) y =
      (Real.rpow 3 (1 / 3) : ℝ) * Real.pi *
        DLMF.Airy.scorerHi ((Real.rpow 3 (-(1 / 3)) : ℝ) * y) := by
  sorry

end DLMF.AsymptoticApproximations
