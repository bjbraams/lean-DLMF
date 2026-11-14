/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.SturmZeros
public import DLMF.Bessel.Asymptotics

/-!
# Positive Bessel zeros at arbitrary real orders

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 7, Theorem 7.7,
asserts simplicity and a complete increasing unbounded sequence of positive zeros
for every real order, including orders at or below negative one.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace DLMF.Bessel

/-- Zeros of a nontrivial analytic Bessel solution away from the singular point are simple.
Temme, *Special Functions*, Chapter 9, Theorem 9.1; Duverney Chapter 7,
Theorem 7.7, synopsis DU-7.09. -/
theorem deriv_ne_zero_of_bessel_solution_eq_zero {ν : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconnected : IsPreconnected U) (hU0 : ∀ z ∈ U, z ≠ 0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hode : ∀ z ∈ U, z ^ 2 * iteratedDeriv 2 f z + z * deriv f z +
      (z ^ 2 - ν ^ 2) * f z = 0) (hnontrivial : ∃ z ∈ U, f z ≠ 0)
    {z : ℂ} (hz : z ∈ U) (hzero : f z = 0) : deriv f z ≠ 0 := by
  sorry

/-- Zeros of the derivative of a nontrivial analytic Bessel solution are simple away
from `0` and the turning points `z²=ν²`.
Temme, *Special Functions*, Chapter 9, Theorem 9.1. -/
theorem iteratedDeriv_two_ne_zero_of_bessel_solution_deriv_eq_zero {ν : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconnected : IsPreconnected U) (hU0 : ∀ z ∈ U, z ≠ 0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hode : ∀ z ∈ U, z ^ 2 * iteratedDeriv 2 f z + z * deriv f z +
      (z ^ 2 - ν ^ 2) * f z = 0) (hnontrivial : ∃ z ∈ U, f z ≠ 0)
    {z : ℂ} (hz : z ∈ U) (hturning : z ^ 2 ≠ ν ^ 2) (hzero : deriv f z = 0) :
    iteratedDeriv 2 f z ≠ 0 := by
  sorry

/-- Every positive zero of `J_ν` is simple for arbitrary real order.
Duverney Chapter 7, Theorem 7.7, synopsis DU-7.09. -/
theorem deriv_re_besselJ_ne_zero_of_eq_zero (ν : ℝ) {x : ℝ} (hx : 0 < x)
    (hzero : Complex.besselJ ν x = 0) :
    deriv (fun t : ℝ => (Complex.besselJ ν t).re) x ≠ 0 := by
  sorry

/-- The positive zeros of a Bessel function of arbitrary real order admit a complete,
strictly increasing enumeration tending to infinity.
Duverney Chapter 7, Theorem 7.7, synopsis DU-7.09. -/
theorem exists_strictMono_besselJ_positive_zeros (ν : ℝ) :
    ∃ z : ℕ → ℝ, StrictMono z ∧ Tendsto z atTop atTop ∧
      (∀ n : ℕ, 0 < z n ∧ Complex.besselJ ν (z n) = 0) ∧
      ∀ x : ℝ, (0 < x ∧ Complex.besselJ ν x = 0) ↔ ∃ n : ℕ, z n = x := by
  sorry

end DLMF.Bessel
