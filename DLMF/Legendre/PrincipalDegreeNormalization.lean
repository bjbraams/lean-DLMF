/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Recurrences
public import DLMF.Legendre.Basic.Associated
public import DLMF.Hypergeometric.ParameterHolomorphy
public import DLMF.Core.Basic
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Meromorphic.Basic

/-!
# Degree dependence and the principal large-argument normalization

The Hobson normalization retains its degree poles. The full expansion allows
vanishing initial reciprocal-Gamma coefficients; the leading-term equivalent
requires the displayed coefficient to be nonzero. Source: Kristensson,
*Second Order Differential Equations*, Chapter 6, (6.1)–(6.4), pp. 107–108.
-/

@[expose] public noncomputable section

open Complex Filter Asymptotics DLMF.Core DLMF.Hypergeometric
open scoped Real Topology

namespace DLMF.Legendre

/-- For each principal-cut argument, the first-kind Legendre function is entire
in its degree. Kristensson, Chapter 6, (6.1)–(6.3), pp. 107–108. -/
theorem differentiable_legendreP_degree {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    Differentiable ℂ (fun ν : ℂ => legendreP ν z) := by
  exact differentiable_regularizedGaussHypergeometric_comp
    (by fun_prop) (by fun_prop) (by fun_prop) (mem_cutPlane_of_one_add hz)

/-- The defining exterior Gauss series gives the complete uniform large-argument
Hobson expansion. A zero initial reciprocal-Gamma coefficient causes no false
nonzero-leading-term assertion. Kristensson, Chapter 6, (6.4), p. 108. -/
theorem hasAsymptoticExpansion_associatedQ_zero_order (ν : ℂ)
    (hν : LegendreQRegular ν 0) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    HasAsymptoticExpansion (sector (Real.pi - δ))
      (fun n z => z ^ (-ν - 1 - 2 * n))
      (fun n => (Real.sqrt Real.pi : ℂ) * Gamma (ν + 1) /
        (2 : ℂ) ^ (ν + 1) * pochhammer ((ν + 2) / 2) n * pochhammer ((ν + 1) / 2) n /
          (n.factorial * Gamma (ν + 3 / 2 + n)))
      (associatedQ ν 0) := by
  sorry

/-- The leading exterior equivalent holds when neither its degree Gamma factor
nor its reciprocal lower-parameter Gamma factor is singular. Kristensson,
Chapter 6, (6.4), p. 108. At a vanishing leading coefficient use the full expansion. -/
theorem associatedQ_zero_order_isEquivalent (ν : ℂ) (hν : LegendreQRegular ν 0)
    (hlower : ∀ n : ℕ, ν + 3 / 2 ≠ -(n : ℂ))
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    associatedQ ν 0 ~[sector (Real.pi - δ)] fun z : ℂ =>
      (Real.sqrt Real.pi : ℂ) * Gamma (ν + 1) /
        ((2 : ℂ) ^ (ν + 1) * Gamma (ν + 3 / 2)) * z ^ (-ν - 1) := by
  sorry

/-- The Hobson function is analytic in degree away from its classical degree
poles. Kristensson, Chapter 6, (6.4), p. 108. -/
theorem analyticAt_associatedQ_degree {ν z : ℂ} (hν : LegendreQRegular ν 0)
    (hz : z - 1 ∈ slitPlane) : AnalyticAt ℂ (fun v : ℂ => associatedQ v 0 z) ν := by
  sorry

/-- The regular degree limits, including every nonnegative integer degree.
Kristensson, Chapter 6, Theorem 6.2, pp. 112–115. -/
theorem tendsto_associatedQ_degree {ν z : ℂ} (hν : LegendreQRegular ν 0)
    (hz : z - 1 ∈ slitPlane) :
    Tendsto (fun v : ℂ => associatedQ v 0 z) (𝓝 ν) (𝓝 (associatedQ ν 0 z)) :=
  (analyticAt_associatedQ_degree hν hz).continuousAt.tendsto

/-- The degree dependence is meromorphic even at the excluded classical poles.
Kristensson, Chapter 6, (6.4), p. 108, and Appendix A, (A.1)–(A.3). -/
theorem meromorphicAt_associatedQ_degree (ν : ℂ) {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    MeromorphicAt (fun v : ℂ => associatedQ v 0 z) ν := by
  sorry

/-- At degree `-1` the Hobson function has a genuine simple pole with residue one.
This is not a removable integer-degree contour quotient. Kristensson,
Chapter 6, (6.4), p. 108, with the Gamma residue of Appendix A, (A.1)–(A.3). -/
theorem tendsto_add_one_mul_associatedQ_degree_neg_one {z : ℂ}
    (hz : z - 1 ∈ slitPlane) :
    Tendsto (fun v : ℂ => (v + 1) * associatedQ v 0 z) (𝓝[≠] (-1)) (𝓝 1) := by
  sorry

end DLMF.Legendre
