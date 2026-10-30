/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Summability.Basic
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Summability of series: regularity and Tauberian theorems (DLMF §1.15(ii), §1.15(viii))

DLMF §1.15(ii) states that the Abel, Cesàro, general Cesàro and Borel methods of §1.15(i) are
regular: a convergent series is summable by each of them to its sum. Convergence of a series is
convergence of its partial sums (`seriesPartialSum`), not Mathlib's unconditional `HasSum`.

Proved: regularity of the Abel method (from Mathlib's Abel limit theorem
`Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`) and of the (C,1) method (from Mathlib's
`Filter.Tendsto.cesaro_smul`). Admitted: regularity of the (C,α) and Borel methods, and the
Tauberian theorems 1.15.54–1.15.57 (Littlewood's theorem and the Hardy–Littlewood theorem).
-/

@[expose] public noncomputable section

open Complex Set Filter Topology Finset

namespace DLMF.AlgebraicAnalytic

/-- DLMF 1.15.10–1.15.11 (regularity of Abel summation, Abel's theorem): if `∑ a_n = s`
(convergent partial sums), then `∑ a_n = s (A)`. Proved from Mathlib's
`Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`. -/
@[dlmf 1.15.E10, dlmf 1.15.E11]
theorem hasAbelSum_of_tendsto {a : ℕ → ℂ} {s : ℂ}
    (h : Tendsto (seriesPartialSum a) atTop (𝓝 s)) : HasAbelSum a s := by
  have h' : Tendsto (fun n => ∑ i ∈ range n, a i) atTop (𝓝 s) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    exact h
  refine ⟨fun x hx => ?_, ?_⟩
  · -- the terms are bounded, so `∑ a_n xⁿ` converges absolutely for `0 < x < 1`
    have hlim : Tendsto a atTop (𝓝 0) := by
      have := (tendsto_add_atTop_iff_nat 1).mpr h'
      have hd := this.sub h'
      rw [sub_self] at hd
      refine hd.congr fun n => ?_
      simp [sum_range_succ]
    obtain ⟨C, hC⟩ := (hlim.norm).bddAbove_range
    have hx0 : 0 ≤ x := hx.1.le
    have hg : Summable fun n : ℕ => C * x ^ n :=
      (summable_geometric_of_lt_one hx0 hx.2).mul_left C
    refine Summable.of_norm_bounded hg fun n => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    exact mul_le_mul_of_nonneg_right (hC ⟨n, rfl⟩) (pow_nonneg hx0 n)
  · have := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt h'
    rw [tendsto_map'_iff] at this
    exact this

/-- DLMF §1.15(ii) (regularity of Cesàro summation): if `∑ a_n = s`, then `∑ a_n = s (C,1)`.
Proved from Mathlib's `Filter.Tendsto.cesaro_smul`. -/
@[dlmf 1.15.ii]
theorem hasCesaroSum_of_tendsto {a : ℕ → ℂ} {s : ℂ}
    (h : Tendsto (seriesPartialSum a) atTop (𝓝 s)) : HasCesaroSum a s := by
  have hc := h.cesaro_smul
  have hc' := (tendsto_add_atTop_iff_nat 1).mpr hc
  refine hc'.congr fun n => ?_
  unfold cesaroMean
  rw [Complex.real_smul, div_eq_inv_mul]
  push_cast
  ring

/-- DLMF §1.15(ii) (regularity of general Cesàro summation): for `α > -1`, if `∑ a_n = s` then
`∑ a_n = s (C,α)`. -/
@[dlmf 1.15.ii]
theorem hasCesaroSumOfOrder_of_tendsto {α : ℝ} (hα : -1 < α) {a : ℕ → ℂ} {s : ℂ}
    (h : Tendsto (seriesPartialSum a) atTop (𝓝 s)) : HasCesaroSumOfOrder α a s := by
  sorry

/-- DLMF §1.15(ii) (regularity of Borel summation): if `∑ a_n = s` then `∑ a_n = s (B)`. -/
@[dlmf 1.15.ii]
theorem hasBorelSum_of_tendsto {a : ℕ → ℂ} {s : ℂ}
    (h : Tendsto (seriesPartialSum a) atTop (𝓝 s)) : HasBorelSum a s := by
  sorry

/-- DLMF 1.15.54–1.15.55 (Littlewood's Tauberian theorem): if `∑ a_n = s (A)` for real `a_n`
and `a_n > -K/n` for `n > 0` with a constant `K > 0`, then `∑ a_n = s`. -/
@[dlmf 1.15.E54, dlmf 1.15.E55]
theorem tendsto_of_hasAbelSum_of_lower_bound {a : ℕ → ℝ} {s : ℝ} {K : ℝ} (hK : 0 < K)
    (hA : HasAbelSum (fun n => (a n : ℂ)) s) (hb : ∀ n : ℕ, 0 < n → -K / n < a n) :
    Tendsto (fun n => ∑ k ∈ range (n + 1), a k) atTop (𝓝 s) := by
  sorry

/-- DLMF 1.15.56–1.15.57 (Hardy–Littlewood Tauberian theorem): if
`lim_{x→1-} (1 - x) ∑ a_n xⁿ = s` for real `a_n` (the series converging for `0 < x < 1`) and
either `|a_n| ≤ K` for all `n` or `a_n ≥ 0` for all `n`, then
`lim_{n→∞} (a_0 + ⋯ + a_n)/(n + 1) = s`. -/
@[dlmf 1.15.E56, dlmf 1.15.E57]
theorem tendsto_cesaro_of_abel_mean {a : ℕ → ℝ} {s : ℝ}
    (hsum : ∀ x ∈ Ioo (0 : ℝ) 1, Summable fun n => a n * x ^ n)
    (hA : Tendsto (fun x : ℝ => (1 - x) * ∑' n, a n * x ^ n) (𝓝[<] 1) (𝓝 s))
    (hb : (∃ K : ℝ, ∀ n, |a n| ≤ K) ∨ ∀ n, 0 ≤ a n) :
    Tendsto (fun n : ℕ => (∑ k ∈ range (n + 1), a k) / (n + 1)) atTop (𝓝 s) := by
  sorry

end DLMF.AlgebraicAnalytic
