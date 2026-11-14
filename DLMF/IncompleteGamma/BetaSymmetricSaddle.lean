/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.BetaAsymptotics
public import DLMFMathlib.Analysis.Analytic.QuadraticInverse
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Taylor coefficients of the symmetric beta saddle

Temme, *Special Functions* (1996), Chapter 11, equations (11.45)–(11.46),
pages 292–294. These derivative-based coefficients supplement the canonical
coefficients extracted from the incomplete-beta asymptotic remainder.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Real Topology

namespace DLMF.Statistical

/-- The entropy phase normalized to vanish at the beta saddle.
Temme (11.45), synopsis TEM-11-14. -/
def betaSymmetricPhase (s : ℝ) (t : ℂ) : ℂ :=
  -(s : ℂ) * log (t / s) - (1 - s : ℂ) * log ((1 - t) / (1 - s))

/-- The inverse branch with `t'(0)=i√(s(1-s))`.
Temme (11.45), synopsis TEM-11-14. -/
def betaSymmetricSaddleInverse (s : ℝ) : ℂ → ℂ :=
  quadraticInverse (betaSymmetricPhase s) s (I * _root_.Real.sqrt (s * (1 - s)))

/-- The pole-subtracted beta amplitude, filled at its removable pole.
Temme (11.45)–(11.46), synopsis TEM-11-14. -/
def betaSymmetricSaddleAmplitude (s x : ℝ) (u : ℂ) : ℂ :=
  let η := Real.betaEta s x
  let raw := fun v : ℂ => deriv (betaSymmetricSaddleInverse s) v /
    (betaSymmetricSaddleInverse s v - x) - (v + I * η)⁻¹
  if u = -I * η then limUnder (𝓝[≠] u) raw else raw u

/-- The explicit derivative algorithm for the symmetric beta coefficients.
Temme (11.46), synopsis TEM-11-14. -/
def betaSymmetricSaddleCoefficient (n : ℕ) (s x : ℝ) : ℂ :=
  -I * ((2 * n - 1).doubleFactorial : ℂ) *
    iteratedDeriv (2 * n) (betaSymmetricSaddleAmplitude s x) 0 / (2 * n).factorial

/-- The defining entropy phase. -/
theorem betaSymmetricPhase_def (s : ℝ) (t : ℂ) :
    betaSymmetricPhase s t =
      -(s : ℂ) * log (t / s) - (1 - s : ℂ) * log ((1 - t) / (1 - s)) := rfl

/-- The defining normalized quadratic inverse. -/
theorem betaSymmetricSaddleInverse_def (s : ℝ) :
    betaSymmetricSaddleInverse s =
      quadraticInverse (betaSymmetricPhase s) s (I * _root_.Real.sqrt (s * (1 - s))) := rfl

/-- The defining pole-subtracted amplitude. -/
theorem betaSymmetricSaddleAmplitude_def (s x : ℝ) (u : ℂ) :
    betaSymmetricSaddleAmplitude s x u =
      let η := Real.betaEta s x
      let raw := fun v : ℂ => deriv (betaSymmetricSaddleInverse s) v /
        (betaSymmetricSaddleInverse s v - x) - (v + I * η)⁻¹
      if u = -I * η then limUnder (𝓝[≠] u) raw else raw u := rfl

/-- The defining Taylor-derivative coefficient. -/
theorem betaSymmetricSaddleCoefficient_def (n : ℕ) (s x : ℝ) :
    betaSymmetricSaddleCoefficient n s x =
      -I * ((2 * n - 1).doubleFactorial : ℂ) *
        iteratedDeriv (2 * n) (betaSymmetricSaddleAmplitude s x) 0 /
          (2 * n).factorial := rfl

/-- The inverse germ satisfies the precise phase equation and imaginary normalization.
Temme (11.45), synopsis TEM-11-14. -/
theorem betaSymmetricSaddleInverse_spec {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    IsAnalyticSaddleMap (betaSymmetricPhase s) (fun u => -u ^ 2 / 2) 0 s
      (I * _root_.Real.sqrt (s * (1 - s))) (betaSymmetricSaddleInverse s) := by
  sorry

/-- Pole subtraction is analytic, including at the central beta transition.
Temme (11.45)–(11.46), synopsis TEM-11-14. -/
theorem analyticAt_betaSymmetricSaddleAmplitude {s x : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hx : 0 < x) (hx1 : x < 1) :
    AnalyticAt ℂ (betaSymmetricSaddleAmplitude s x) 0 := by
  sorry

/-- The explicit Taylor algorithm agrees with the canonical asymptotic coefficients.
The alternating factor accounts for the canonical DLMF normalization.
Temme (11.46), synopsis TEM-11-14. -/
theorem betaSymmetricSaddleCoefficient_eq (n : ℕ) {s x : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hx : 0 < x) (hx1 : x < 1) :
    betaSymmetricSaddleCoefficient n s x =
      (-1 : ℂ) ^ n * betaSymmetricC n s (Real.betaEta s x) := by
  sorry

end DLMF.Statistical
