/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.ExpIntegralAsymptotics
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion

/-!
# The enveloping exponential-integral expansion

Temme, *Special Functions* (1996), Chapter 2, equation (2.4), pages 31–32,
synopsis TEM-02-05. The factorial expansion is divergent at every fixed positive
argument, although every finite truncation has a signed first-omitted-term bound.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology

namespace DLMF.Confluent.Real

/-- The real scaled exponential integral `x exp(x) E₁(x)` for positive `x`.
Temme (2.4), synopsis TEM-02-05. -/
def envelopingExpIntegral (x : ℝ) : ℝ :=
  x * _root_.Real.exp x * (expIntegralE 1 x).re

/-- The exact ordinary integral remainder in the factorial expansion.
Temme (2.4), synopsis TEM-02-05. -/
def envelopingExpIntegralRemainder (N : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ N * N.factorial * x * _root_.Real.exp x *
    ∫ t : ℝ in Ioi x, _root_.Real.exp (-t) * t ^ (-((N : ℝ) + 1))

/-- The defining scaled exponential integral. -/
theorem envelopingExpIntegral_def (x : ℝ) :
    envelopingExpIntegral x = x * _root_.Real.exp x * (expIntegralE 1 x).re := rfl

/-- The defining actual integral remainder. -/
theorem envelopingExpIntegralRemainder_def (N : ℕ) (x : ℝ) :
    envelopingExpIntegralRemainder N x =
      (-1 : ℝ) ^ N * N.factorial * x * _root_.Real.exp x *
        ∫ t : ℝ in Ioi x, _root_.Real.exp (-t) * t ^ (-((N : ℝ) + 1)) := rfl

/-- The book's improper integral is the existing exponential integral.
Temme (2.4), synopsis TEM-02-05. -/
theorem envelopingExpIntegral_eq_integral {x : ℝ} (hx : 0 < x) :
    envelopingExpIntegral x = x * _root_.Real.exp x *
      ∫ t : ℝ in Ioi x, _root_.Real.exp (-t) / t := by
  sorry

/-- The exact finite factorial expansion with its ordinary integral remainder.
Temme (2.4), synopsis TEM-02-05. -/
theorem envelopingExpIntegral_eq_sum_add_remainder (N : ℕ) {x : ℝ} (hx : 0 < x) :
    envelopingExpIntegral x =
      (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * n.factorial / x ^ n) +
        envelopingExpIntegralRemainder N x := by
  sorry

/-- Every finite remainder has the sign of its first omitted term, strictly.
Temme (2.4), synopsis TEM-02-05. -/
theorem envelopingExpIntegralRemainder_sign (N : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (-1 : ℝ) ^ N * envelopingExpIntegralRemainder N x := by
  sorry

/-- The absolute remainder is at most the first omitted term.
Temme (2.4), synopsis TEM-02-05. -/
theorem abs_envelopingExpIntegralRemainder_le (N : ℕ) {x : ℝ} (hx : 0 < x) :
    |envelopingExpIntegralRemainder N x| ≤ N.factorial / x ^ N := by
  sorry

/-- The factorial series is a complete asymptotic expansion at positive infinity.
Temme (2.4), synopsis TEM-02-05. -/
theorem hasAsymptoticExpansion_envelopingExpIntegral :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => x ^ (-(n : ℝ)))
      (fun n : ℕ => (-1 : ℝ) ^ n * n.factorial) envelopingExpIntegral := by
  intro N
  have hsum (x : ℝ) (hx : 0 < x) :
      (∑ n ∈ Finset.range N, x ^ (-(n : ℝ)) •
        ((-1 : ℝ) ^ n * n.factorial)) =
      ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * n.factorial / x ^ n := by
    apply Finset.sum_congr rfl
    intro n _
    simp only [smul_eq_mul, _root_.Real.rpow_neg hx.le, _root_.Real.rpow_natCast]
    ring
  apply IsBigO.of_bound (N.factorial : ℝ)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [hsum x hx, envelopingExpIntegral_eq_sum_add_remainder N hx, add_sub_cancel_left]
  simpa only [_root_.Real.norm_eq_abs, _root_.Real.rpow_neg hx.le, _root_.Real.rpow_natCast,
    abs_inv, abs_pow, abs_of_pos hx, div_eq_mul_inv] using
      abs_envelopingExpIntegralRemainder_le N hx

/-- At every fixed positive argument the factorial terms fail to tend to zero;
consequently their natural ordered series diverges. Temme (2.4), synopsis TEM-02-05. -/
theorem not_tendsto_envelopingExpIntegral_terms {x : ℝ} (hx : 0 < x) :
    ¬ Tendsto (fun n : ℕ => (-1 : ℝ) ^ n * n.factorial / x ^ n) atTop (𝓝 0) := by
  sorry

end DLMF.Confluent.Real
