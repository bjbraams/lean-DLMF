/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Bounds for decaying powers

A lower bound for the norm of a complex base bounds its principal powers with nonpositive
real exponent. Real translated powers admit a product majorant suited to summation.
-/

@[expose] public section

open scoped Real

namespace Complex

/-- A positive norm lower bound controls a principal power with nonpositive real exponent. -/
lemma norm_cpow_le_of_norm_lower_bound {z s : ℂ} {r : ℝ} (hr : 0 < r) (hz : r ≤ ‖z‖)
    (hs : s.re ≤ 0) : ‖z ^ s‖ ≤ r ^ s.re * Real.exp (π * |s.im|) := by
  refine (norm_cpow_le _ _).trans ?_
  rw [div_eq_mul_inv, ← Real.exp_neg]
  have h1 : ‖z‖ ^ s.re ≤ r ^ s.re := Real.rpow_le_rpow_of_nonpos hr hz hs
  have h2 : Real.exp (-(arg z * s.im)) ≤ Real.exp (π * |s.im|) := by
    rw [Real.exp_le_exp]
    calc -(arg z * s.im) ≤ |arg z| * |s.im| := by rw [← abs_mul]; exact neg_le_abs _
      _ ≤ π * |s.im| := mul_le_mul_of_nonneg_right (abs_arg_le_pi z) (abs_nonneg _)
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (Real.rpow_nonneg hr.le _)

/-- The real power of a norm is bounded by the norm of the principal power and a phase factor. -/
lemma rpow_norm_le_norm_cpow_mul_exp {z : ℂ} (hz : z ≠ 0) (s : ℂ) :
    ‖z‖ ^ s.re ≤ ‖z ^ s‖ * Real.exp (π * |s.im|) := by
  rw [norm_cpow_of_ne_zero hz, div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
  apply le_mul_of_one_le_right (Real.rpow_nonneg (norm_nonneg z) _)
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (abs_arg_le_pi z) (abs_nonneg s.im)
  nlinarith [le_abs_self (arg z * s.im), abs_mul (arg z) s.im]

end Complex

namespace Real

/-- A decaying translated power separates into two powers of half its degree. -/
lemma add_rpow_le_mul_rpow_half {r t p : ℝ} (hr : 1 ≤ r) (ht : 0 ≤ t) (hp : 0 ≤ p) :
    (r + t) ^ (-p) ≤ r ^ (-p / 2) * (t + 1) ^ (-p / 2) := by
  have hr0 : 0 < r := by linarith
  have hrt : 0 < r + t := by positivity
  have hsq : r * (t + 1) ≤ (r + t) ^ 2 := by
    have h1 : r ≤ r + t := by linarith
    have h2 : t + 1 ≤ r + t := by linarith
    nlinarith [mul_le_mul h1 h2 (by positivity : 0 ≤ t + 1) hrt.le]
  rw [← Real.mul_rpow hr0.le (by positivity)]
  calc (r + t) ^ (-p) = ((r + t) ^ 2) ^ (-p / 2) := by
        rw [← Real.rpow_natCast_mul hrt.le]
        congr 1
        norm_num
        ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) hsq (by linarith)

end Real

namespace Asymptotics

/-- Integer powers are ordered by their exponents at infinity in a normed division ring. -/
lemma isBigO_zpow_zpow_cobounded_of_le {𝕜 : Type*} [NormedDivisionRing 𝕜]
    {m n : ℤ} (hmn : m ≤ n) :
    (fun z : 𝕜 => z ^ m) =O[Bornology.cobounded 𝕜] (fun z => z ^ n) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_cobounded_le_norm (E := 𝕜) 1] with z hz
  simpa only [norm_zpow, one_mul, Real.rpow_intCast] using
    (Real.rpow_le_rpow_of_exponent_le hz (Int.cast_le.mpr hmn))

end Asymptotics
