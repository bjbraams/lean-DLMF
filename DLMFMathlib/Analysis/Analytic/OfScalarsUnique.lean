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

Uniqueness of the coefficients of one-variable scalar power series, the exponential series in
`ℂ` and `ℝ`, and a nonvanishing criterion for sums of nonnegative real series.

## Main results

* `FormalMultilinearSeries.eq_ofScalars_coeff`: a one-variable series is `ofScalars` of its
  coefficients;
* `RCLike.eq_zero_of_hasSum_mul_pow_ball`, `RCLike.eq_of_hasSum_mul_pow_ball`: scalar
  power-series coefficients over `ℝ` or `ℂ` are determined by their sums on a small ball;
  the existing `Complex` forms are specializations;
* `RCLike.eq_of_hasSum_mul_pow_mul_ball`: uniqueness for series supported on multiples
  of a positive natural number;
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

namespace RCLike

/-- Scalar power-series coefficients over `ℝ` or `ℂ` vanish when their sums vanish on a ball. -/
lemma eq_zero_of_hasSum_mul_pow_ball {K : Type*} [RCLike K] {e : ℕ → K} {r : ℝ}
    (hr : 0 < r) (h : ∀ z : K, ‖z‖ < r → HasSum (fun n => e n * z ^ n) 0) : e = 0 := by
  have hrad : ENNReal.ofReal r ≤ (ofScalars K e).radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    have ht' : (t : ℝ) < r := by
      rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hr] at ht
    have hs := (h ((t : ℝ) : K) (by simpa using ht')).summable.tendsto_atTop_zero.norm
    refine (ofScalars K e).le_radius_of_tendsto (l := 0) ?_
    simpa [ofScalars_norm, norm_mul, norm_pow] using hs
  have hp : HasFPowerSeriesOnBall (fun _ => (0 : K)) (ofScalars K e) 0 (ENNReal.ofReal r) :=
    { r_le := hrad
      r_pos := ENNReal.ofReal_pos.2 hr
      hasSum := fun {y} hy => by
        rw [Metric.eball_ofReal, mem_ball_zero_iff] at hy
        simpa [ofScalars_apply_eq, mul_comm] using h y hy }
  exact (ofScalars_series_eq_zero K).1 hp.hasFPowerSeriesAt.eq_zero

/-- Two scalar power series over `ℝ` or `ℂ` with equal sums on a ball have equal coefficients. -/
lemma eq_of_hasSum_mul_pow_ball {K : Type*} [RCLike K] {c d : ℕ → K} {g : K → K} {r : ℝ}
    (hr : 0 < r) (hc : ∀ z : K, ‖z‖ < r → HasSum (fun n => c n * z ^ n) (g z))
    (hd : ∀ z : K, ‖z‖ < r → HasSum (fun n => d n * z ^ n) (g z)) : c = d := by
  have h := eq_zero_of_hasSum_mul_pow_ball (e := c - d) hr fun z hz => by
    simpa [sub_mul] using (hc z hz).sub (hd z hz)
  exact sub_eq_zero.mp h



/-- Coefficients are determined by a power series supported at positive multiples of a fixed
natural number, over either `ℝ` or `ℂ`. -/
lemma eq_of_hasSum_mul_pow_mul_ball {K : Type*} [RCLike K] {c d : ℕ → K} {g : K → K}
    {r : ℝ} {q : ℕ} (hr : 0 < r) (hq : 0 < q)
    (hc : ∀ z : K, ‖z‖ < r → HasSum (fun n => c n * z ^ (q * n)) (g z))
    (hd : ∀ z : K, ‖z‖ < r → HasSum (fun n => d n * z ^ (q * n)) (g z)) : c = d := by
  let C : ℕ → K := fun n => if q ∣ n then c (n / q) else 0
  let D : ℕ → K := fun n => if q ∣ n then d (n / q) else 0
  have hinj : Function.Injective (fun n : ℕ => q * n) := by
    intro n m he
    exact Nat.eq_of_mul_eq_mul_left hq he
  have hC (z : K) (hz : ‖z‖ < r) : HasSum (fun n => C n * z ^ n) (g z) := by
    refine (hinj.hasSum_iff fun n hn => ?_).mp ?_
    · have hnot : ¬q ∣ n := by
        rintro ⟨m, rfl⟩
        exact hn ⟨m, rfl⟩
      simp only [C, ite_eq_right hnot, zero_mul]
    · simpa only [Function.comp_def, C, Nat.dvd_mul_right, ↓reduceIte,
        Nat.mul_div_right _ hq] using hc z hz
  have hD (z : K) (hz : ‖z‖ < r) : HasSum (fun n => D n * z ^ n) (g z) := by
    refine (hinj.hasSum_iff fun n hn => ?_).mp ?_
    · have hnot : ¬q ∣ n := by
        rintro ⟨m, rfl⟩
        exact hn ⟨m, rfl⟩
      simp only [D, ite_eq_right hnot, zero_mul]
    · simpa only [Function.comp_def, D, Nat.dvd_mul_right, ↓reduceIte,
        Nat.mul_div_right _ hq] using hd z hz
  have he := RCLike.eq_of_hasSum_mul_pow_ball hr hC hD
  funext n
  have he' := congrFun he (q * n)
  simpa only [C, D, Nat.dvd_mul_right, ↓reduceIte, Nat.mul_div_right _ hq] using he'

end RCLike

namespace Complex

/-- If `∑ eₙ zⁿ = 0` on a disk `‖z‖ < r`, then all coefficients `eₙ` vanish. -/
theorem eq_zero_of_hasSum_mul_pow_ball {e : ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => e n * z ^ n) 0) : e = 0 := by
  exact RCLike.eq_zero_of_hasSum_mul_pow_ball hr h

/-- Two scalar power series with the same sums on a disk `‖z‖ < ρ` have the same
coefficients. -/
theorem eq_of_hasSum_mul_pow_ball {c d : ℕ → ℂ} {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => c n * z ^ n) (g z))
    (hd : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => d n * z ^ n) (g z)) : c = d := by
  exact RCLike.eq_of_hasSum_mul_pow_ball hρ hc hd

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
