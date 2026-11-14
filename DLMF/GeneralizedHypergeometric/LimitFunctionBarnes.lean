/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# A Barnes integral for the hypergeometric limit function

Kristensson, *Second Order Differential Equations*, Chapter 7, Theorem 7.3,
pp. 134–135. Absolute convergence holds on the negative real argument axis for
the stated vertical-line range; no open complex sector of absolute convergence
is asserted for this `₀F₁` Barnes integrand.
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace DLMF.Hypergeometric

/-- Kristensson, Chapter 7, Theorem 7.3: absolute convergence of the upward
vertical-line Barnes integral when `(1-Re c)/2 < σ < 0` and `z<0`. -/
theorem integrable_limitFunction_barnes {c : ℂ} {σ z : ℝ}
    (hc : 1 < c.re) (hσ : (1 - c.re) / 2 < σ) (hσ0 : σ < 0) (hz : z < 0) :
    Integrable (fun t : ℝ => Gamma (-((σ : ℂ) + t * I)) *
      (-(z : ℂ)) ^ ((σ : ℂ) + t * I) / Gamma (c + σ + t * I)) := by
  sorry

/-- Kristensson, Chapter 7, Theorem 7.3, pp. 134–135: the Barnes representation
of `₀F₁(;c;z)`, expressed directly with Mathlib's regularized hypergeometric series. -/
theorem limitFunction_eq_barnes_integral {c : ℂ} {σ z : ℝ}
    (hc : 1 < c.re) (hσ : (1 - c.re) / 2 < σ) (hσ0 : σ < 0) (hz : z < 0) :
    Gamma c * regularizedHGFun (∅ : Multiset ℂ) {c} z =
      Gamma c / (2 * Real.pi) * ∫ t : ℝ, Gamma (-((σ : ℂ) + t * I)) *
        (-(z : ℂ)) ^ ((σ : ℂ) + t * I) / Gamma (c + σ + t * I) := by
  sorry

/-- Kristensson, Chapter 7, Theorem 7.3: the symmetric truncated Barnes
integrals converge locally uniformly for negative real arguments. -/
theorem tendstoLocallyUniformlyOn_limitFunction_barnes {c : ℂ} {σ : ℝ}
    (hc : 1 < c.re) (hσ : (1 - c.re) / 2 < σ) (hσ0 : σ < 0) :
    TendstoLocallyUniformlyOn
      (fun R : ℝ => fun z : ℝ => Gamma c / (2 * Real.pi) *
        ∫ t : ℝ in -R..R, Gamma (-((σ : ℂ) + t * I)) *
          (-(z : ℂ)) ^ ((σ : ℂ) + t * I) / Gamma (c + σ + t * I))
      (fun z : ℝ => Gamma c * regularizedHGFun (∅ : Multiset ℂ) {c} z)
      atTop (Iio 0) := by
  sorry

end DLMF.Hypergeometric
