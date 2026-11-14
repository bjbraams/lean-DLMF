/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.UniformAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Gamma integrals in real and Hankel saddle coordinates

Temme, *Special Functions* (1996), §3.7, (3.34)–(3.38), pp. 69–71,
synopsis TEM-03-11. Removable coordinate values at the saddle are explicit.
-/

@[expose] public noncomputable section
open Complex Filter MeasureTheory Set
open scoped Real Topology
namespace DLMF.Gamma

/-- The real Gamma saddle coordinate, Temme (3.34)–(3.38), TEM-03-11.
Its mathematical domain is `t>0`; it is normalized to increase through zero at `t=1`. -/
def Real.gammaSaddleCoordinate (t : ℝ) : ℝ :=
  (if t < 1 then -1 else 1) * Real.sqrt (2 * (t - Real.log t - 1))

/-- The real inverse Gamma saddle coordinate, Temme (3.34)–(3.38), TEM-03-11. -/
def Real.gammaSaddleInverse (u : ℝ) : ℝ :=
  Classical.epsilon (fun t : ℝ => 0 < t ∧ Real.gammaSaddleCoordinate t = u)

/-- The defining signed-square-root coordinate, Temme (3.34)–(3.38). -/
theorem Real.gammaSaddleCoordinate_def (t : ℝ) : Real.gammaSaddleCoordinate t =
    (if t < 1 then -1 else 1) * Real.sqrt (2 * (t - Real.log t - 1)) := rfl

/-- The inverse's defining positive-coordinate specification, Temme (3.34)–(3.38). -/
theorem Real.gammaSaddleInverse_def (u : ℝ) : Real.gammaSaddleInverse u =
    Classical.epsilon (fun t : ℝ => 0 < t ∧ Real.gammaSaddleCoordinate t = u) := rfl

/-- The saddle coordinate is an increasing bijection onto the real line,
Temme (3.34)–(3.38), synopsis TEM-03-11. -/
theorem Real.gammaSaddleCoordinate_strictMonoOn_bijOn :
    StrictMonoOn Real.gammaSaddleCoordinate (Ioi 0) ∧
      BijOn Real.gammaSaddleCoordinate (Ioi 0) univ := by
  sorry

/-- The real coordinate agrees with the canonical logarithmic-plane branch,
Temme (3.34)–(3.38), synopses TEM-03-11 and TEM-11-07. -/
theorem Real.gammaSaddleCoordinate_eq_gammaUniformEtaOnLog {t : ℝ} (ht : 0 < t) :
    (Real.gammaSaddleCoordinate t : ℂ) = DLMF.Confluent.gammaUniformEtaOnLog (log t) := by
  sorry

/-- The inverse is positive, has the specified coordinate, and takes zero to one,
Temme (3.34)–(3.38), synopsis TEM-03-11. -/
theorem Real.gammaSaddleInverse_spec (u : ℝ) :
    0 < Real.gammaSaddleInverse u ∧
      Real.gammaSaddleCoordinate (Real.gammaSaddleInverse u) = u ∧
      Real.gammaSaddleInverse 0 = 1 := by
  sorry

/-- Analytic inversion at the Gamma saddle, Temme (3.34)–(3.38), TEM-03-11. -/
theorem Real.analyticAt_gammaSaddleInverse_zero : AnalyticAt ℝ Real.gammaSaddleInverse 0 := by
  sorry

/-- The inverse-coordinate derivative, including the removable value one,
Temme (3.34)–(3.38), synopsis TEM-03-11. -/
theorem Real.hasDerivAt_gammaSaddleInverse (u : ℝ) :
    HasDerivAt Real.gammaSaddleInverse
      (if u = 0 then 1 else u * Real.gammaSaddleInverse u / (Real.gammaSaddleInverse u - 1)) u := by
  sorry

/-- The Gamma integral after its Gaussian saddle substitution,
Temme (3.34)–(3.38), synopsis TEM-03-11. -/
theorem Real.Gamma_eq_gaussian_saddle_integral {x : ℝ} (hx : 0 < x) :
    Integrable (fun u : ℝ => Real.exp (-x * u ^ 2 / 2) * deriv Real.gammaSaddleInverse u) ∧
      Real.Gamma (x + 1) = x ^ (x + 1) * Real.exp (-x) *
        ∫ u : ℝ, Real.exp (-x * u ^ 2 / 2) * deriv Real.gammaSaddleInverse u := by
  sorry

/-! The reciprocal-Gamma steepest-descent integral of Temme (3.37)–(3.38)
is already `DLMF.Gamma.recip_Gamma_binet` in
`DLMF.Gamma.IntegralRepresentations.HankelAndGaussian`, with the explicit
logarithmic contour `binetPathLog`. Its value at the single removable point
does not affect the integral. -/

end DLMF.Gamma
