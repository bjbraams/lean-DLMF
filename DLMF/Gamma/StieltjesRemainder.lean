/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling
public import DLMFMathlib.Analysis.EulerMaclaurin
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Stieltjes's remainder for the logarithmic Stirling expansion

The exact periodic-Bernoulli integral, sharp angular majorant and positive-axis
first-omitted-term bound of Olver, *Asymptotics and Special Functions*,
Chapter 8, §4, pp. 293–295. The logarithm is TauCeti's analytic `logGamma`, real
on the positive axis, rather than the principal logarithm of a Gamma value.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Finset
open scoped Real Nat

namespace DLMF.Gamma

/-- The logarithmic Stirling remainder after the terms with indices `1 <= k < m`.
Its integral formula is used only for `m >= 1` on the principal slit plane.
Olver, Chapter 8, §4, p. 293. -/
def logGammaStieltjesRemainder (m : ℕ) (z : ℂ) : ℂ :=
  TauCeti.logGamma z - ((z - 1 / 2) * log z - z + (Real.log (2 * Real.pi) / 2 : ℝ)) -
    ∑ k ∈ Icc 1 (m - 1), (bernoulli (2 * k) : ℂ) /
      ((2 * k : ℂ) * (2 * k - 1) * z ^ (2 * k - 1))

/-- The defining residual of the logarithmic Stirling expansion. -/
theorem logGammaStieltjesRemainder_def (m : ℕ) (z : ℂ) :
    logGammaStieltjesRemainder m z =
      TauCeti.logGamma z - ((z - 1 / 2) * log z - z + (Real.log (2 * Real.pi) / 2 : ℝ)) -
        ∑ k ∈ Icc 1 (m - 1), (bernoulli (2 * k) : ℂ) /
          ((2 * k : ℂ) * (2 * k - 1) * z ^ (2 * k - 1)) := rfl

/-- The periodic-Bernoulli integrand is absolutely integrable on the principal cut
for every positive remainder index. Olver, Chapter 8, §4, p. 293. -/
theorem integrableOn_logGammaStieltjesRemainder {m : ℕ} (hm : 1 ≤ m)
    {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ =>
      ((bernoulli (2 * m) : ℂ) - periodicBernoulli (2 * m) t) /
        ((2 * m : ℂ) * ((t : ℂ) + z) ^ (2 * m))) (Ioi 0) := by
  sorry

/-- Stieltjes's exact integral remainder on the principal slit plane.
Olver, Chapter 8, §4, p. 293. -/
theorem logGammaStieltjesRemainder_eq_integral {m : ℕ} (hm : 1 ≤ m)
    {z : ℂ} (hz : z ∈ slitPlane) :
    logGammaStieltjesRemainder m z =
      ∫ t in Ioi (0 : ℝ),
        ((bernoulli (2 * m) : ℂ) - periodicBernoulli (2 * m) t) /
          ((2 * m : ℂ) * ((t : ℂ) + z) ^ (2 * m)) := by
  sorry

/-- The sharp angular Stieltjes bound, retaining its explicit secant power.
Olver, Chapter 8, §4, pp. 293–294. -/
theorem norm_logGammaStieltjesRemainder_le {m : ℕ} (hm : 1 ≤ m)
    {z : ℂ} (hz : z ∈ slitPlane) :
    ‖logGammaStieltjesRemainder m z‖ ≤
      |(bernoulli (2 * m) : ℝ)| * (Real.cos (arg z / 2))⁻¹ ^ (2 * m) /
        ((2 * m : ℝ) * (2 * m - 1) * ‖z‖ ^ (2 * m - 1)) := by
  sorry

/-- On the positive axis Stieltjes's remainder has the strict sign and smaller
magnitude of the first omitted Bernoulli term. Olver, Chapter 8, §4, p. 294. -/
theorem logGammaStieltjesRemainder_sign_and_norm_lt {m : ℕ} (hm : 1 ≤ m)
    {x : ℝ} (hx : 0 < x) :
    (logGammaStieltjesRemainder m x).im = 0 ∧
      0 < (bernoulli (2 * m) : ℝ) * (logGammaStieltjesRemainder m x).re ∧
      ‖logGammaStieltjesRemainder m x‖ <
        |(bernoulli (2 * m) : ℝ)| /
          ((2 * m : ℝ) * (2 * m - 1) * x ^ (2 * m - 1)) := by
  sorry

end DLMF.Gamma
