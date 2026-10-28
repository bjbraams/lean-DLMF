/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.PSeriesComplex

/-!
# Two facts about the Riemann zeta function

* `riemannZeta_six`: `ζ(6) = π⁶/945`;
* `hasSum_neg_one_pow_div_nat_add_one_cpow`: the alternating (Dirichlet eta) series
  `∑ (-1)ⁿ (n+1)^{-s}` converges to `(1 - 2^{1-s}) ζ(s)` for `Re s > 1`.
-/

@[expose] public section
open Complex
open scoped Real

/-- `ζ(6) = π⁶/945`, from Mathlib's `riemannZeta_two_mul_nat`. -/
theorem riemannZeta_six : riemannZeta 6 = π ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  have hb : bernoulli 6 = 1 / 42 := by decide +kernel
  norm_num [hb, Nat.factorial] at h
  rw [h]; ring

/-- The Dirichlet eta series: `∑ (-1)ⁿ / (n+1)^s = (1 - 2^{1-s}) ζ(s)` for `Re s > 1`. -/
theorem hasSum_neg_one_pow_div_nat_add_one_cpow {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s)
      ((1 - 2 ^ (1 - s)) * riemannZeta s) := by
  set a : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with ha
  have hsum : Summable a := by
    have := Complex.summable_one_div_nat_cpow.mpr hs
    have h1 := (summable_nat_add_iff 1).mpr this
    simp only [Nat.cast_add, Nat.cast_one] at h1
    exact h1
  have hz : riemannZeta s = ∑' n, a n := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hodd : ∀ k : ℕ, a (2 * k + 1) = 2 ^ (-s) * a k := fun k => by
    simp only [ha]
    rw [show ((2 * k + 1 : ℕ) : ℂ) + 1 = ((2 : ℝ) : ℂ) * ((k + 1 : ℝ) : ℂ) by push_cast; ring,
      mul_cpow_ofReal_nonneg (by norm_num) (by positivity), cpow_neg]
    push_cast
    field_simp
  have hO : HasSum (fun k => a (2 * k + 1)) (2 ^ (-s) * riemannZeta s) := by
    simp_rw [hodd, hz]; exact hsum.hasSum.mul_left _
  have hE : HasSum (fun k => a (2 * k)) ((1 - 2 ^ (-s)) * riemannZeta s) := by
    have hEs : Summable (fun k => a (2 * k)) :=
      hsum.comp_injective (fun i j h => by omega)
    have h := tsum_even_add_odd hEs hO.summable
    rw [← hz, hO.tsum_eq] at h
    convert hEs.hasSum using 1
    linear_combination -h
  have hE' : HasSum (fun k : ℕ => (-1 : ℂ) ^ (2 * k) / (((2 * k : ℕ) : ℂ) + 1) ^ s)
      ((1 - 2 ^ (-s)) * riemannZeta s) := by
    convert hE using 2 with k; simp [ha, pow_mul]
  have hO' : HasSum (fun k : ℕ => (-1 : ℂ) ^ (2 * k + 1) / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s)
      (-(2 ^ (-s) * riemannZeta s)) := by
    convert hO.neg using 2 with k; simp [ha, pow_succ, pow_mul, neg_div]
  have h := HasSum.even_add_odd (f := fun n : ℕ => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s) hE' hO'
  convert h using 1
  rw [show (1 : ℂ) - s = 1 + -s by ring, cpow_add _ _ two_ne_zero, cpow_one]
  ring
