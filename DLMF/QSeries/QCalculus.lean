/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.Calculus
public import DLMF.QSeries.Pochhammer

/-!
# `q`-derivative and the `q`-fundamental theorem (Duverney §10.1.2)

`qDeriv q f x = (f(x) - f(qx))/((1-q)x)` is Jackson's `q`-derivative. This file proves
`δ_q xⁿ = [n]_q x^{n-1}`, linearity, the `q`-product rule, and `δ_q f(x) → f'(x)` as `q → 1`.
It also proves both halves of the `q`-fundamental theorem of calculus for the existing Jackson
integral `jacksonIntegral`: `δ_q ∫₀ˣ f d_q t = f(x)` and `∫₀ˣ δ_q f d_q t = f(x) - f(0)`.
-/

@[expose] public section

open Complex Finset Filter
open scoped Topology

noncomputable section

namespace DLMF.QSeries

/-- `δ_q xⁿ = [n]_q x^{n-1}` (Duverney (10.11)). -/
theorem qDeriv_pow {q x : ℂ} (hq : q ≠ 1) (hx : x ≠ 0) (n : ℕ) :
    qDeriv q (fun t => t ^ n) x = qNum q n * x ^ (n - 1) := by
  have hq' : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  rcases n with _ | n
  · simp [qDeriv, qNum]
  simp only [qDeriv, qNum, mul_pow, Nat.add_sub_cancel, pow_succ]
  field_simp

/-- The `q`-product rule `δ_q(uv)(x) = δ_q u(x) v(x) + u(qx) δ_q v(x)` (Duverney (10.14)). -/
theorem qDeriv_mul (q : ℂ) (u v : ℂ → ℂ) (x : ℂ) :
    qDeriv q (fun t => u t * v t) x = qDeriv q u x * v x + u (q * x) * qDeriv q v x := by
  simp only [qDeriv]
  rw [div_mul_eq_mul_div, mul_div_assoc', ← add_div]
  congr 1; ring

/-- Linearity of `δ_q`. -/
theorem qDeriv_add (q : ℂ) (u v : ℂ → ℂ) (x : ℂ) :
    qDeriv q (fun t => u t + v t) x = qDeriv q u x + qDeriv q v x := by
  simp only [qDeriv]; rw [← add_div]; congr 1; ring

/-- Homogeneity of `δ_q`. -/
theorem qDeriv_const_mul (q c : ℂ) (u : ℂ → ℂ) (x : ℂ) :
    qDeriv q (fun t => c * u t) x = c * qDeriv q u x := by
  simp only [qDeriv]; rw [mul_div_assoc']; congr 1; ring

/-- `δ_q f(x) → f'(x)` as `q → 1` (Duverney (10.12)). -/
@[dlmf 17.2.iv "partial: q-derivative limit away from zero; extended origin convention handled by the proved local adapter"]
theorem tendsto_qDeriv {f : ℂ → ℂ} {f' x : ℂ} (hf : HasDerivAt f f' x) (hx : x ≠ 0) :
    Tendsto (fun q => qDeriv q f x) (𝓝[≠] 1) (𝓝 f') := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hf
  have hmap : Tendsto (fun q : ℂ => q * x) (𝓝[≠] 1) (𝓝[≠] x) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Tendsto (fun q : ℂ => q * x) (𝓝 1) (𝓝 x) := by
        have hcont : Continuous fun q : ℂ => q * x := by fun_prop
        simpa using hcont.tendsto (1 : ℂ)
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq ⊢
      intro h
      exact hq (by simpa [hx] using congrArg (· / x) h)
  refine (hs.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [Function.comp, slope_def_field, qDeriv]
  have hq' : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  rw [show q * x - x = -((1 - q) * x) by ring, show f (q * x) - f x = -(f x - f (q * x)) by ring,
    neg_div_neg_eq]

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
