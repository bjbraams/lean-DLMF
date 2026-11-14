/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.AnalyticProperties
public import DLMF.GeneralizedHypergeometric.Derivatives
public import DLMF.Gamma.Polygamma

/-!
# Recognition and parameter differentiation of hypergeometric series

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 3, Theorem 3.3
and Exercise 3.5. Lower parameters avoid the nonpositive integers. Parameter
derivative formulas are stated on the actual open convergence region, retaining
the unrestricted complex argument when the upper count is at most the lower count.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Topology

namespace DLMF.Hypergeometric

/-- The empty hypergeometric function is the exponential.
Duverney (3.5), synopsis DU-3.04. -/
theorem generalizedHypergeometric_empty_empty (z : ℂ) :
    generalizedHypergeometric 0 0 z = exp z := by
  sorry

/-- The principal binomial hypergeometric function on the full cut plane.
Duverney (3.7), synopsis DU-3.04. -/
theorem generalizedHypergeometric_singleton_empty (a : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    generalizedHypergeometric {a} 0 z = (1 - z) ^ (-a) := by
  sorry

/-- The continued Gauss logarithm identity on the full cut plane.
Duverney (3.19), synopsis DU-3.04. -/
theorem mul_regularizedGaussHypergeometric_one_one_two {z : ℂ} (hz : z ∈ cutPlane) :
    z * regularizedGaussHypergeometric 1 1 2 z = -log (1 - z) := by
  sorry

/-- The arctangent hypergeometric identity on the entire real axis, using the principal
continuation rather than the totalized Gauss series outside its disk.
Duverney (4.12), synopsis DU-4.03. -/
theorem arctan_eq_regularizedGaussHypergeometric (x : ℝ) :
    (Real.arctan x : ℂ) = x * Gamma (3 / 2) *
      regularizedGaussHypergeometric 1 (1 / 2) (3 / 2) (-(x : ℂ) ^ 2) := by
  sorry

/-- Recognition by a rational consecutive-coefficient ratio, with the original radius
retained. Duverney Theorem 3.3, equations (3.10)–(3.11), synopsis DU-3.03. -/
theorem eq_generalizedHypergeometric_of_coefficient_recurrence
    (a b : Multiset ℂ) (hb : LowerParametersRegular b) {A : ℂ} (hA : A ≠ 0)
    {c : ℕ → ℂ} {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ∀ n : ℕ, c (n + 1) = A * c n * (a.map (fun α : ℂ => α + n)).prod /
      (((n : ℂ) + 1) * (b.map (fun β : ℂ => β + n)).prod))
    (hf : ∀ z : ℂ, ‖z‖ < R → HasSum (fun n => c n * z ^ n) (f z))
    {z : ℂ} (hz : ‖z‖ < R) :
    f z = c 0 * generalizedHypergeometric a b (A * z) := by
  sorry

/-- The explicit upper-parameter derivative series, locally valid on the open convergence
region. Duverney Chapter 3, Exercise 3.5, synopsis DU-3.16. -/
theorem hasDerivAt_generalizedHypergeometric_upper_parameter
    (a b : Multiset ℂ) (hb : LowerParametersRegular b) {α z : ℂ}
    (hα : ∀ n : ℕ, α ≠ -(n : ℂ)) (hcount : a.card ≤ b.card)
    (hz : a.card + 1 ≤ b.card ∨ ‖z‖ < 1) :
    HasDerivAt (fun w => generalizedHypergeometric (w ::ₘ a) b z)
      (∑' n : ℕ, generalizedHypergeometricCoeff (α ::ₘ a) b n * z ^ n *
        (digamma (α + n) - digamma α)) α := by
  sorry

/-- Absolute convergence of the upper-parameter derivative series.
Duverney Chapter 3, Exercise 3.5, synopsis DU-3.16. -/
theorem summable_generalizedHypergeometric_upper_parameter_derivative
    (a b : Multiset ℂ) (hb : LowerParametersRegular b) {α z : ℂ}
    (hα : ∀ n : ℕ, α ≠ -(n : ℂ)) (hcount : a.card ≤ b.card)
    (hz : a.card + 1 ≤ b.card ∨ ‖z‖ < 1) :
    Summable (fun n : ℕ => generalizedHypergeometricCoeff (α ::ₘ a) b n * z ^ n *
      (digamma (α + n) - digamma α)) := by
  sorry

/-- The explicit lower-parameter derivative series, with the opposite digamma difference.
Duverney Chapter 3, Exercise 3.5, synopsis DU-3.16. -/
theorem hasDerivAt_generalizedHypergeometric_lower_parameter
    (a b : Multiset ℂ) {β z : ℂ} (hb : LowerParametersRegular (β ::ₘ b))
    (hcount : a.card ≤ b.card + 2) (hz : a.card ≤ b.card + 1 ∨ ‖z‖ < 1) :
    HasDerivAt (fun w => generalizedHypergeometric a (w ::ₘ b) z)
      (∑' n : ℕ, generalizedHypergeometricCoeff a (β ::ₘ b) n * z ^ n *
        (digamma β - digamma (β + n))) β := by
  sorry

/-- Absolute convergence of the lower-parameter derivative series.
Duverney Chapter 3, Exercise 3.5, synopsis DU-3.16. -/
theorem summable_generalizedHypergeometric_lower_parameter_derivative
    (a b : Multiset ℂ) {β z : ℂ} (hb : LowerParametersRegular (β ::ₘ b))
    (hcount : a.card ≤ b.card + 2) (hz : a.card ≤ b.card + 1 ∨ ‖z‖ < 1) :
    Summable (fun n : ℕ => generalizedHypergeometricCoeff a (β ::ₘ b) n * z ^ n *
      (digamma β - digamma (β + n))) := by
  sorry

end DLMF.Hypergeometric
