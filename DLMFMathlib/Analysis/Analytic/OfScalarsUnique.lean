/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.Basic

/-!
# Scalar power series: uniqueness of coefficients and the exponential series

* `FormalMultilinearSeries.eq_ofScalars_coeff`: a one-variable series is `ofScalars` of its
  coefficients;
* `Complex.eq_zero_of_hasSum_mul_pow_ball`, `Complex.eq_of_hasSum_mul_pow_ball`: the
  coefficients of a scalar power series are determined by its sums on a small disk;
* `Complex.hasSum_pow_div_factorial`, `Real.hasSum_pow_div_factorial`: the exponential
  series;
* `Complex.ne_zero_of_hasSum_ofReal_of_nonneg`: a series of nonnegative reals with positive
  leading term has nonzero sum.
-/

@[expose] public section
open FormalMultilinearSeries
open scoped Nat

/-- A one-variable formal power series is `ofScalars` of its coefficients. -/
theorem FormalMultilinearSeries.eq_ofScalars_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    p = ofScalars ℂ (fun n => p.coeff n) := by
  ext n
  rw [apply_eq_prod_smul_coeff]
  simp [ofScalars, mul_comm]

namespace Complex

/-- If `∑ eₙ zⁿ = 0` on a disk `‖z‖ < r`, then all coefficients `eₙ` vanish. -/
theorem eq_zero_of_hasSum_mul_pow_ball {e : ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => e n * z ^ n) 0) : e = 0 := by
  have hrad : ENNReal.ofReal r ≤ (ofScalars ℂ e).radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    have ht' : (t : ℝ) < r := by
      rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hr] at ht
    have hs := (h (t : ℂ) (by simpa using ht')).summable.tendsto_atTop_zero.norm
    refine (ofScalars ℂ e).le_radius_of_tendsto (l := 0) ?_
    simpa [ofScalars_norm, norm_mul, norm_pow] using hs
  have hp : HasFPowerSeriesOnBall (fun _ => (0 : ℂ)) (ofScalars ℂ e) 0 (ENNReal.ofReal r) :=
    { r_le := hrad
      r_pos := ENNReal.ofReal_pos.2 hr
      hasSum := fun {y} hy => by
        rw [Metric.eball_ofReal, mem_ball_zero_iff] at hy
        simpa [ofScalars_apply_eq, mul_comm] using h y hy }
  exact (ofScalars_series_eq_zero ℂ).1 hp.hasFPowerSeriesAt.eq_zero

/-- Two scalar power series with the same sums on a disk `‖z‖ < ρ` have the same
coefficients. -/
theorem eq_of_hasSum_mul_pow_ball {c d : ℕ → ℂ} {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => c n * z ^ n) (g z))
    (hd : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => d n * z ^ n) (g z)) : c = d := by
  have h := eq_zero_of_hasSum_mul_pow_ball (e := c - d) hρ fun z hz => by
    simpa [sub_mul] using (hc z hz).sub (hd z hz)
  exact sub_eq_zero.mp h

/-- The exponential series: `∑ wⁿ / n! = e^w` in `ℂ`. -/
theorem hasSum_pow_div_factorial (w : ℂ) : HasSum (fun n => w ^ n / (n ! : ℂ)) (exp w) := by
  rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp w

/-- A series of nonnegative reals, viewed in `ℂ`, with positive first term has a nonzero
sum. -/
theorem ne_zero_of_hasSum_ofReal_of_nonneg {f : ℕ → ℝ} {S : ℂ}
    (h : HasSum (fun k => (f k : ℂ)) S) (hf : ∀ k, 0 ≤ f k) (h0 : 0 < f 0) : S ≠ 0 := by
  have hr : HasSum f S.re := by simpa using Complex.reCLM.hasSum h
  intro hS
  rw [hS, zero_re] at hr
  have := le_hasSum hr 0 fun j _ => hf j
  linarith

end Complex

/-- The exponential series: `∑ Rⁿ / n! = e^R` in `ℝ`. -/
theorem Real.hasSum_pow_div_factorial (R : ℝ) :
    HasSum (fun n => R ^ n / (n ! : ℝ)) (Real.exp R) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp R
