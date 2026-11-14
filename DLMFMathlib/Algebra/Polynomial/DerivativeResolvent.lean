/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# The finite polynomial resolvent of differentiation

Olver, *Asymptotics and Special Functions*, Chapter 14, §3,
pp. 523–526, synopsis O-14.02. The inverse of c-D on polynomials is a finite
derivative sum; no convergence of an infinite operator series is needed.
Mathlib `Polynomial.sumIDeriv` is the unweighted c=1 case; the weighted
resolvent is needed for the general coefficient equations.
-/

@[expose] public noncomputable section
namespace Polynomial
variable {K : Type*} [Field K]

/-- The finite inverse-differentiation sum for c-D, with c nonzero in applications.
Olver, Chapter 14, §3, pp. 523–526. -/
def derivativeResolvent (c : K) (p : K[X]) : K[X] :=
  ∑ j ∈ Finset.range (p.natDegree + 1), C ((c ^ (j + 1))⁻¹) * (derivative^[j]) p

/-- The defining finite derivative sum. -/
theorem derivativeResolvent_def (c : K) (p : K[X]) : derivativeResolvent c p =
    ∑ j ∈ Finset.range (p.natDegree + 1), C ((c ^ (j + 1))⁻¹) * (derivative^[j]) p := rfl

/-- The finite derivative sum solves its first-order polynomial equation.
Olver, Chapter 14, §3, pp. 523–526. -/
theorem mul_derivativeResolvent_sub_derivative {c : K} (hc : c ≠ 0) (p : K[X]) :
    C c * derivativeResolvent c p - (derivativeResolvent c p).derivative = p := by
  sorry

/-- Polynomial solutions of c*y-y'=p are unique when c is nonzero.
Olver, Chapter 14, §3, pp. 523–526. -/
theorem mul_sub_derivative_eq_iff {c : K} (hc : c ≠ 0) (p r : K[X]) :
    C c * r - r.derivative = p ↔ r = derivativeResolvent c p := by
  sorry

/-- The differential resolvent does not increase the polynomial degree.
Olver, Chapter 14, §3, pp. 523–526. -/
theorem natDegree_derivativeResolvent_le (c : K) (p : K[X]) :
    (derivativeResolvent c p).natDegree ≤ p.natDegree := by
  sorry

end Polynomial
