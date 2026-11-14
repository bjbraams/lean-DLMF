/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.SpecialValues
public import DLMF.Elliptic.JacobiIdentities

/-!
# Incomplete cubic and quartic elliptic reductions

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 5, equations
(5.60)–(5.68), expresses real algebraic integrals using Jacobi's inverse sine.
The functions in this area take the parameter `m=k²`, whereas the source uses the modulus.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology Real

namespace DLMF.Elliptic

/-- Incomplete lemniscate reduction with parameter `m=1/2`.
Duverney (5.60)–(5.61), synopsis DU-5.14. -/
theorem integral_recip_sqrt_one_sub_pow_four_to {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∫ t in (0 : ℝ)..x, (Real.sqrt (1 - t ^ 4))⁻¹ =
      (Real.completeEllipticKOfParameter (1 / 2) -
        Real.jacobiArcsnOfParameter (Real.sqrt (1 - x ^ 2)) (1 / 2)) / Real.sqrt 2 := by
  sorry

/-- Incomplete positive quartic reduction with parameter `m=1/2`.
Duverney (5.62), synopsis DU-5.14. -/
theorem integral_recip_sqrt_one_add_pow_four {x : ℝ} (hx : |x| ≤ 1) :
    ∫ t in (0 : ℝ)..x, (Real.sqrt (1 + t ^ 4))⁻¹ =
      Real.jacobiArcsnOfParameter (2 * x / (1 + x ^ 2)) (1 / 2) / 2 := by
  sorry

/-- The finite interval reduction of a biquadratic integral.
Duverney (5.63)–(5.64), synopsis DU-5.14. -/
theorem integral_recip_sqrt_sub_sq_mul_sub_sq {a b x : ℝ}
    (ha : 0 < a) (hab : a < b) (hx : x ∈ Icc (0 : ℝ) a) :
    ∫ t in (0 : ℝ)..x, (Real.sqrt ((a ^ 2 - t ^ 2) * (b ^ 2 - t ^ 2)))⁻¹ =
      Real.jacobiArcsnOfParameter (x / a) ((a / b) ^ 2) / b := by
  sorry

/-- The exterior reduction of a biquadratic integral, with absolute convergence.
Duverney (5.65)–(5.66), synopsis DU-5.14. -/
theorem integral_Ioi_recip_sqrt_sq_sub_mul_sq_sub {a b x : ℝ}
    (ha : 0 < a) (hab : a < b) (hbx : b < x) :
    IntegrableOn (fun t : ℝ => (Real.sqrt ((t ^ 2 - a ^ 2) * (t ^ 2 - b ^ 2)))⁻¹)
      (Ioi x) ∧
      (∫ t in Ioi x, (Real.sqrt ((t ^ 2 - a ^ 2) * (t ^ 2 - b ^ 2)))⁻¹) =
        Real.jacobiArcsnOfParameter (b / x) ((a / b) ^ 2) / b := by
  sorry

/-- A cubic integral with three ordered real roots.
Duverney (5.67)–(5.68), synopsis DU-5.15. -/
theorem integral_recip_sqrt_cubic {a b c x : ℝ} (hab : a < b) (hbc : b < c)
    (hx : x ∈ Icc a b) :
    ∫ t in a..x, (Real.sqrt ((t - a) * (t - b) * (t - c)))⁻¹ =
      2 * Real.jacobiArcsnOfParameter (Real.sqrt ((x - a) / (b - a)))
        ((b - a) / (c - a)) / Real.sqrt (c - a) := by
  sorry

end DLMF.Elliptic
