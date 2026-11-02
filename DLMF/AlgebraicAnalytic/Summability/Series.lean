/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Summability.Basic
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Complex.AbelLimit

/-!
# Summability of series: regularity and Tauberian theorems (DLMF §1.15(ii), §1.15(viii))

DLMF §1.15(ii) states that the Abel, Cesàro, general Cesàro and Borel methods of §1.15(i) are
regular: a convergent series is summable by each of them to its sum. Convergence of a series is
convergence of its partial sums (`seriesPartialSum`), not Mathlib's unconditional `HasSum`.

## Main results

* `hasAbelSum_of_tendsto`: regularity of the Abel method (DLMF 1.15.10–1.15.11), from Mathlib's
  Abel limit theorem `Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`.
* `hasCesaroSum_of_tendsto`: regularity of the (C,1) method, from Mathlib's
  `Filter.Tendsto.cesaro_smul`.
* `hasCesaroSumOfOrder_of_tendsto`, `hasBorelSum_of_tendsto`: regularity of the (C,α) and
  Borel methods.
* `tendsto_of_hasAbelSum_of_lower_bound`: Littlewood's Tauberian theorem
  (DLMF 1.15.54–1.15.55).
* `tendsto_cesaro_of_abel_mean`: the Hardy–Littlewood Tauberian theorem (DLMF 1.15.56–1.15.57).
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

/-- DLMF §1.15(ii) (regularity of general Cesàro summation): for `α ≥ 0`,
a series with convergent partial sums is `(C,α)`-summable to the same sum. Negative orders
are not regular, despite the larger range in which the means are defined. -/
@[dlmf 1.15.ii]
theorem hasCesaroSumOfOrder_of_tendsto {α : ℝ} (hα : 0 ≤ α) {a : ℕ → ℂ} {s : ℂ}
    (h : Tendsto (seriesPartialSum a) atTop (𝓝 s)) : HasCesaroSumOfOrder α a s := by
  sorry

/-- DLMF §1.15(ii) (regularity of Borel summation): if `∑ a_n = s` then `∑ a_n = s (B)`. -/
@[dlmf 1.15.ii]
theorem hasBorelSum_of_tendsto {a : ℕ → ℂ} {s : ℂ}
    (h : Tendsto (seriesPartialSum a) atTop (𝓝 s)) : HasBorelSum a s := by
  set c := seriesPartialSum a
  have hexpR : ∀ t : ℝ, HasSum (fun n : ℕ => t ^ n / (n.factorial : ℝ)) (Real.exp t) := fun t => by
    have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) t
    rwa [← Real.exp_eq_exp_ℝ] at this
  have hexpC : ∀ t : ℝ, HasSum (fun n : ℕ => (t : ℂ) ^ n / (n.factorial : ℂ)) (Real.exp t : ℂ) :=
    fun t => by
      have := (hexpR t).mapL Complex.ofRealCLM
      simpa using this
  obtain ⟨C, hC⟩ := h.norm.bddAbove_range
  -- summability for every `t`, with a geometric-type majorant
  have hsumm : ∀ (b : ℕ → ℂ) (B : ℝ), (∀ n, ‖b n‖ ≤ B) → ∀ t : ℝ, 0 ≤ t →
      Summable fun n => b n * (t : ℂ) ^ n / (n.factorial : ℂ) := by
    intro b B hB t ht
    refine Summable.of_norm_bounded ((hexpR t).summable.mul_left B) fun n => ?_
    rw [mul_div_assoc, norm_mul, norm_div, norm_pow, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg ht]
    exact mul_le_mul_of_nonneg_right (hB n) (by positivity)
  refine ⟨fun t ht => hsumm c C (fun n => hC ⟨n, rfl⟩) t ht, ?_⟩
  set b : ℕ → ℂ := fun n => c n - s
  have hb : Tendsto b atTop (𝓝 0) := by simpa [b] using h.sub_const s
  obtain ⟨B, hB⟩ := hb.norm.bddAbove_range
  have hB' : ∀ n, ‖b n‖ ≤ B := fun n => hB ⟨n, rfl⟩
  -- the main estimate
  have hmain : Tendsto (fun t : ℝ =>
      (Real.exp (-t) : ℂ) * ∑' n, b n * (t : ℂ) ^ n / (n.factorial : ℂ))
      atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hb) (ε / 2) (by positivity)
    have hpoly : Tendsto (fun t : ℝ => Real.exp (-t) *
        ∑ n ∈ range N, ‖b n‖ * (t ^ n / (n.factorial : ℝ))) atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ => ∑ n ∈ range N, ‖b n‖ / (n.factorial : ℝ) *
          (t ^ n * Real.exp (-t))) atTop (𝓝 (∑ n ∈ range N, ‖b n‖ / (n.factorial : ℝ) * 0)) :=
        tendsto_finsetSum _ fun n _ =>
          (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).const_mul _
      simp only [mul_zero, sum_const_zero] at this
      refine this.congr fun t => ?_
      rw [mul_sum]
      refine sum_congr rfl fun n _ => ?_
      ring
    filter_upwards [hpoly.eventually (gt_mem_nhds (half_pos hε)), eventually_ge_atTop 0]
      with t ht ht0
    rw [dist_zero_right]
    set g : ℕ → ℝ := fun n => (if n < N then ‖b n‖ else 0) * (t ^ n / (n.factorial : ℝ)) +
      ε / 2 * (t ^ n / (n.factorial : ℝ))
    have hgle : ∀ n, ‖b n * (t : ℂ) ^ n / (n.factorial : ℂ)‖ ≤ g n := by
      intro n
      rw [mul_div_assoc, norm_mul, norm_div, norm_pow, Complex.norm_real, Complex.norm_natCast,
        Real.norm_of_nonneg ht0]
      have hw : 0 ≤ t ^ n / (n.factorial : ℝ) := by positivity
      by_cases hn : n < N
      · simp only [g, ite_eq_left_of_eq_true _ _ (eq_true hn)]; nlinarith
      · simp only [g, ite_eq_right_of_eq_false _ _ (eq_false hn), zero_mul, zero_add]
        have := hN n (not_lt.mp hn)
        rw [dist_zero_right] at this
        exact mul_le_mul_of_nonneg_right this.le hw
    have hgs : HasSum g
        (∑ n ∈ range N, ‖b n‖ * (t ^ n / (n.factorial : ℝ)) + ε / 2 * Real.exp t) := by
      refine HasSum.add ?_ ((hexpR t).mul_left _)
      have : HasSum (fun n => (if n < N then ‖b n‖ else 0) * (t ^ n / (n.factorial : ℝ)))
          (∑ n ∈ range N, (if n < N then ‖b n‖ else 0) * (t ^ n / (n.factorial : ℝ))) :=
        hasSum_sum_of_ne_finset_zero (s := range N)
        (f := fun n => (if n < N then ‖b n‖ else 0) * (t ^ n / (n.factorial : ℝ)))
        (fun n hn => by simp only [Finset.mem_range] at hn; simp [hn])
      convert this using 1
      refine sum_congr rfl fun n hn => ?_
      simp [Finset.mem_range.mp hn]
    have hsb := hsumm b B hB' t ht0
    calc ‖(Real.exp (-t) : ℂ) * ∑' n, b n * (t : ℂ) ^ n / (n.factorial : ℂ)‖
        = Real.exp (-t) * ‖∑' n, b n * (t : ℂ) ^ n / (n.factorial : ℂ)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      _ ≤ Real.exp (-t) * (∑ n ∈ range N, ‖b n‖ * (t ^ n / (n.factorial : ℝ)) +
            ε / 2 * Real.exp t) := by
          gcongr
          exact tsum_of_norm_bounded hgs hgle
      _ = Real.exp (-t) * ∑ n ∈ range N, ‖b n‖ * (t ^ n / (n.factorial : ℝ)) + ε / 2 := by
          rw [mul_add, mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ < ε := by linarith
  refine (hmain.add_const s).congr' ?_ |>.trans (by rw [zero_add])
  filter_upwards [eventually_ge_atTop 0] with t ht
  have hs1 := (hsumm b B hB' t ht).hasSum
  have hs2 := (hexpC t).mul_left s
  have hsum : ∑' n, c n * (t : ℂ) ^ n / (n.factorial : ℂ) =
      ∑' n, b n * (t : ℂ) ^ n / (n.factorial : ℂ) + s * (Real.exp t : ℂ) := by
    refine (((hs1.add hs2).congr_fun fun n => ?_).tsum_eq).symm.symm
    simp only [b]; ring
  rw [hsum, mul_add, ← mul_assoc, mul_comm _ s, mul_assoc, ← Complex.ofReal_mul,
    ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, mul_one]

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
