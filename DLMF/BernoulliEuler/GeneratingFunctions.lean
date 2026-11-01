/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic.GeneratingFunctions
public import DLMF.Elementary.Hyperbolic

/-!
# Euler numbers and polynomials: generating functions on the full disc

This file covers the generating functions of the Euler numbers and polynomials of DLMF §24.2(ii)
on DLMF's full discs. The other results of §24.2 are in
`DLMF.BernoulliEuler.Basic.GeneratingFunctions`.

## Main results

* `hasSum_eulerNumber_mul_pow_div'`: `sech t = ∑ Eₙ tⁿ/n!` on the full disc `|t| < π/2`
  (DLMF 24.2.6).
* `hasSum_eulerPolyE_mul_pow_div`: the generating function of the Euler polynomials on the full
  disc `|t| < π` (DLMF 24.2.8).

## Implementation notes

24.2.6 is the series of `sech` from `DLMF.Elementary.Hyperbolic`; 24.2.8 follows by a Cauchy
product with `e^{xt}`.
-/

@[expose] public section

noncomputable section

open Finset Filter
open scoped Nat Real Topology

namespace DLMF.BernoulliEuler

/-- **DLMF 24.2.6** on DLMF's full disc: `2eᵗ/(e^{2t} + 1) = sech t = ∑ₙ Eₙ tⁿ/n!` for
`|t| < π/2`. (The project's `hasSum_eulerNumber_mul_pow_div`, also tagged 24.2.E6, has radius
`1/2`.) -/
@[dlmf 24.2.E6]
theorem hasSum_eulerNumber_mul_pow_div' {t : ℂ} (ht : ‖t‖ < π / 2) :
    HasSum (fun n : ℕ => (eulerNumber n : ℂ) * t ^ n / n !)
      (2 * Complex.exp t / (Complex.exp (2 * t) + 1)) := by
  have hval : 2 * Complex.exp t / (Complex.exp (2 * t) + 1) = DLMF.Elementary.sech t := by
    rw [DLMF.Elementary.sech, Complex.cosh, show 2 * t = t + t by ring, Complex.exp_add,
      Complex.exp_neg]
    have he : Complex.exp t ≠ 0 := Complex.exp_ne_zero t
    by_cases hc : Complex.exp t * Complex.exp t + 1 = 0
    · have : Complex.exp t + (Complex.exp t)⁻¹ = 0 := by
        field_simp; linear_combination hc
      rw [hc, this]; simp
    · field_simp
  rw [hval]
  have h := DLMF.Elementary.hasSum_sech ht
  have hodd : ∀ n ∉ Set.range (fun k : ℕ => 2 * k),
      (eulerNumber n : ℂ) * t ^ n / n ! = 0 := by
    intro n hn
    have : Odd n := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | h
      · exact absurd ⟨m, by simp only; omega⟩ hn
      · exact h
    simp [eulerNumber_eq_zero_of_odd this]
  refine ((mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0)).hasSum_iff hodd).mp ?_
  refine h.congr_fun fun k => ?_
  simp only [Function.comp]
  ring


/-- **DLMF 24.2.8**: the generating function `2e^{xt}/(eᵗ + 1) = ∑ₙ Eₙ(x) tⁿ/n!` for `|t| < π`,
complex `x`. -/
@[dlmf 24.2.E8]
theorem hasSum_eulerPolyE_mul_pow_div (x : ℂ) {t : ℂ} (ht : ‖t‖ < π) :
    HasSum (fun n : ℕ => eulerPolyE n x * t ^ n / n !)
      (2 * Complex.exp (x * t) / (Complex.exp t + 1)) := by
  have ht2 : ‖t / 2‖ < π / 2 := by
    rw [norm_div, Complex.norm_two]; linarith
  have hsum : ∀ z : ℂ, ‖z‖ < π →
      Summable (fun n => ((eulerNumber n : ℂ) / 2 ^ n / n !) * z ^ n) := by
    intro z hz
    have hz2 : ‖z / 2‖ < π / 2 := by rw [norm_div, Complex.norm_two]; linarith
    exact ((hasSum_eulerNumber_mul_pow_div' hz2).congr_fun fun n => by
      rw [div_pow]; ring).summable
  have hE := hasSum_eulerNumber_mul_pow_div' ht2
  have hE' : HasSum (fun n : ℕ => ((eulerNumber n : ℂ) / 2 ^ n) * t ^ n / n !)
      (2 * Complex.exp (t / 2) / (Complex.exp (2 * (t / 2)) + 1)) :=
    hE.congr_fun fun n => by rw [div_pow]; ring
  have hs : Summable fun n => ‖((eulerNumber n : ℂ) / 2 ^ n) * t ^ n / (n ! : ℂ)‖ := by
    refine (summable_norm_mul_pow_of_summable hsum ht).congr fun n => ?_
    congr 1; ring
  have h := hasSum_binomialConv_mul_exp (w := x - 1 / 2) hs hE'
  have hval : 2 * Complex.exp (t / 2) / (Complex.exp (2 * (t / 2)) + 1) *
      Complex.exp ((x - 1 / 2) * t) = 2 * Complex.exp (x * t) / (Complex.exp t + 1) := by
    rw [show 2 * (t / 2) = t by ring, div_mul_eq_mul_div, mul_assoc, ← Complex.exp_add,
      show t / 2 + (x - 1 / 2) * t = x * t by ring]
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  rw [eulerPolyE_eq_sum]

end DLMF.BernoulliEuler
