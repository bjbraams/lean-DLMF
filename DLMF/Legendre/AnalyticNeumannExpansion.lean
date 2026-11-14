/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Sums
public import DLMFMathlib.Analysis.Complex.Joukowski

/-!
# Analytic Heine and Neumann expansions in confocal ellipses

Integer-degree `Q_n` has its full branch outside the focal segment, including
the negative real exterior. The ellipse path is the affine transform of the
existing canonical Joukowski parametrization. Source: Olver, *Asymptotics and
Special Functions*, Chapter 12, Exercises 13.1–13.2, p. 473.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Real Topology

namespace DLMF.Legendre

/-- The positively oriented confocal ellipse with foci `-1,1`, parametrized over
`0<=t<=2*pi`, with outer radius `R>1`. Olver, Chapter 12, Exercise13.2, p. 473. -/
def ellipsePath (R t : ℝ) : ℂ := 2 * Complex.Joukowski.ellipseParametrization R t - 1

/-- The defining affine Joukowski ellipse. -/
theorem ellipsePath_def (R t : ℝ) : ellipsePath R t =
    2 * Complex.Joukowski.ellipseParametrization R t - 1 := rfl

/-- The Legendre coefficient of an analytic function, normalized for the
unweighted interval `[-1,1]`. Olver, Chapter 12, Exercise13.2, p. 473. -/
def analyticLegendreCoefficient (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 1 / 2) * ∫ x : ℝ in (-1)..1,
    f x * DLMF.OrthogonalPolynomials.legendrePolynomialP n x

/-- The defining interval coefficient. -/
theorem analyticLegendreCoefficient_def (f : ℂ → ℂ) (n : ℕ) :
    analyticLegendreCoefficient f n = ((n : ℂ) + 1 / 2) * ∫ x : ℝ in (-1)..1,
      f x * DLMF.OrthogonalPolynomials.legendrePolynomialP n x := rfl

/-- Heine's expansion on the full exterior branch of integer-degree `Q`,
uniformly on separated closed confocal ellipses. The exterior set is unbounded.
Olver, Chapter 12, Exercise13.1, p. 473. -/
theorem legendre_heine_uniform_full_exterior {R S : ℝ} (hR : 1 ≤ R) (hRS : R < S) :
    TendstoUniformlyOn (fun N : ℕ => fun p : ℂ × ℂ => ∑ n ∈ Finset.range N,
      (2 * n + 1 : ℂ) * DLMF.OrthogonalPolynomials.legendrePolynomialP n p.1 *
        associatedQ n 0 p.2) (fun p => (p.2 - p.1)⁻¹) atTop
      {p | legendreEllipseRadius p.1 ≤ R + R⁻¹ ∧ S + S⁻¹ ≤ legendreEllipseRadius p.2} := by
  sorry

/-- The real interval coefficient equals the positively oriented contour
coefficient on every intermediate ellipse. The contour stays inside the analytic
region and outside the focal segment. Olver, Chapter 12, Exercise13.2, p. 473. -/
theorem analyticLegendreCoefficient_eq_contour {f : ℂ → ℂ} {R r : ℝ}
    (hR : 1 < R) (hr : 1 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f {z | legendreEllipseRadius z < R + R⁻¹}) (n : ℕ) :
    analyticLegendreCoefficient f n = (2 * n + 1 : ℂ) / (2 * Real.pi * I) *
      ∫ t : ℝ in 0..(2 * Real.pi), f (ellipsePath r t) * associatedQ n 0 (ellipsePath r t) *
        deriv (ellipsePath r) t := by
  sorry

/-- Neumann's expansion converges uniformly on every strictly smaller closed
ellipse. Analyticity in the open outer ellipse and continuity on its closure
are precisely the source's hypotheses. Olver, Chapter 12, Exercise13.2, p. 473. -/
theorem tendstoUniformlyOn_analyticLegendre_expansion {f : ℂ → ℂ} {R r : ℝ}
    (hR : 1 < R) (hr : 1 ≤ r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f {z | legendreEllipseRadius z < R + R⁻¹})
    (hcontinuous : ContinuousOn f {z | legendreEllipseRadius z ≤ R + R⁻¹}) :
    TendstoUniformlyOn (fun N : ℕ => fun z => ∑ n ∈ Finset.range N,
      analyticLegendreCoefficient f n * DLMF.OrthogonalPolynomials.legendrePolynomialP n z)
      f atTop {z | legendreEllipseRadius z ≤ r + r⁻¹} := by
  sorry

end DLMF.Legendre
