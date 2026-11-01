/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.CalculusProperties
public import DLMF.QSeries.Pochhammer

/-!
# The `q`-derivative and the `q`-fundamental theorem (Duverney §10.1.2)

This file proves both halves of the `q`-fundamental theorem of calculus for Jackson's
`q`-derivative `qDeriv q f x = (f(x) - f(qx))/((1-q)x)` and the Jackson integral
`jacksonIntegral`. The rules for `qDeriv` (powers, linearity, the product rule and the limit
`q → 1`) are in `DLMF.QSeries.Basic.CalculusProperties`.

## Main results

* `qDeriv_jacksonIntegral`: `δ_q ∫₀ˣ f d_q t = f(x)` (Duverney, Theorem 10.4).
* `jacksonIntegral_qDeriv`: `∫₀ˣ δ_q f d_q t = f(x) - f(0)`.
-/

@[expose] public section

open Complex Finset Filter
open scoped Topology

noncomputable section

namespace DLMF.QSeries

/-- **The `q`-fundamental theorem of calculus** (Duverney, Theorem 10.4): the Jackson integral
`F(x) = ∫₀ˣ f d_q t` satisfies `δ_q F = f`, when the defining series converges. -/
theorem qDeriv_jacksonIntegral {q x : ℂ} {f : ℂ → ℂ} (hq : q ≠ 1) (hx : x ≠ 0)
    (hs : Summable fun n : ℕ => f (x * q ^ n) * q ^ n) :
    qDeriv q (fun t => jacksonIntegral q t f) x = f x := by
  have hq' : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hsplit := hs.tsum_eq_zero_add
  have hshift : ∑' n : ℕ, f (x * q ^ (n + 1)) * q ^ (n + 1) =
      q * ∑' n : ℕ, f (q * x * q ^ n) * q ^ n := by
    rw [← tsum_mul_left]; congr 1; funext n; rw [pow_succ]; ring_nf
  simp only [qDeriv, jacksonIntegral]
  rw [hsplit, hshift]
  simp only [pow_zero, mul_one]
  field_simp
  ring

/-- **The `q`-integral of a `q`-derivative**: `∫₀ˣ δ_q f d_q t = f(x) - f(0)` when `f` is
continuous at `0`, `|q| < 1` and the Jackson series converges (Duverney, Theorem 10.4). -/
theorem jacksonIntegral_qDeriv {q x : ℂ} {f : ℂ → ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hx : x ≠ 0)
    (hf : ContinuousAt f 0) (hs : Summable fun n : ℕ => qDeriv q f (x * q ^ n) * q ^ n) :
    jacksonIntegral q x (qDeriv q f) = f x - f 0 := by
  have hq1 : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr (by rintro rfl; simp at hq)
  have hterm (n : ℕ) : qDeriv q f (x * q ^ n) * q ^ n =
      (f (x * q ^ n) - f (x * q ^ (n + 1))) / ((1 - q) * x) := by
    simp only [qDeriv]
    have : q ^ n ≠ 0 := pow_ne_zero n hq0
    rw [show q * (x * q ^ n) = x * q ^ (n + 1) by ring]
    field_simp
  have hlim : Tendsto (fun n : ℕ => f (x * q ^ n)) atTop (𝓝 (f 0)) := by
    have h0 : Tendsto (fun n : ℕ => x * q ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).const_mul x
    exact hf.tendsto.comp h0
  have hpart : Tendsto (fun N : ℕ => ∑ n ∈ range N, qDeriv q f (x * q ^ n) * q ^ n) atTop
      (𝓝 ((f x - f 0) / ((1 - q) * x))) := by
    simp_rw [hterm, ← sum_div, sum_range_sub' (fun n => f (x * q ^ n))]
    simp only [pow_zero, mul_one]
    exact ((tendsto_const_nhds.sub hlim).div_const _)
  have htsum := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hpart
  simp only [jacksonIntegral]
  rw [htsum]
  field_simp

end DLMF.QSeries

end
