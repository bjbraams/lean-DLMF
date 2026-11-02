/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Summability.Basic
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.RingTheory.PowerSeries.Basic

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

/-- Abel summation for the Cesàro means: `∑ A_k a_{n-k} = ∑ B_k s_{n-k}` when
`∑_{k ≤ m} B_k = A_m` for every `m`. -/
private theorem sum_mul_sub_eq_sum_mul_partialSum {A B : ℕ → ℂ} (a : ℕ → ℂ)
    (hB : ∀ m, ∑ k ∈ range (m + 1), B k = A m) (n : ℕ) :
    ∑ k ∈ range (n + 1), A k * a (n - k) =
      ∑ k ∈ range (n + 1), B k * seriesPartialSum a (n - k) := by
  have hA : PowerSeries.mk A = PowerSeries.mk B * PowerSeries.mk (fun _ => (1 : ℂ)) := by
    ext m
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        PowerSeries.coeff i (PowerSeries.mk B) * PowerSeries.coeff j
          (PowerSeries.mk (fun _ => (1 : ℂ))))]
    simp [hB]
  have hs : PowerSeries.mk (seriesPartialSum a) =
      PowerSeries.mk a * PowerSeries.mk (fun _ => (1 : ℂ)) := by
    ext m
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        PowerSeries.coeff i (PowerSeries.mk a) * PowerSeries.coeff j
          (PowerSeries.mk (fun _ => (1 : ℂ))))]
    simp [seriesPartialSum]
  have key : PowerSeries.coeff n (PowerSeries.mk A * PowerSeries.mk a) =
      PowerSeries.coeff n (PowerSeries.mk B * PowerSeries.mk (seriesPartialSum a)) := by
    rw [hA, hs]; ring_nf
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
      PowerSeries.coeff i (PowerSeries.mk A) * PowerSeries.coeff j (PowerSeries.mk a)),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
      PowerSeries.coeff i (PowerSeries.mk B) * PowerSeries.coeff j
        (PowerSeries.mk (seriesPartialSum a)))] at key
  simpa only [PowerSeries.coeff_mk, Nat.succ_eq_add_one] using key

/-- DLMF §1.15(ii) (regularity of general Cesàro summation): for `α ≥ 0`,
a series with convergent partial sums is `(C,α)`-summable to the same sum. Negative orders
are not regular, despite the larger range in which the means are defined. -/
@[dlmf 1.15.ii]
theorem hasCesaroSumOfOrder_of_tendsto {α : ℝ} (hα : 0 ≤ α) {a : ℕ → ℂ} {s : ℂ}
    (h : Tendsto (seriesPartialSum a) atTop (𝓝 s)) : HasCesaroSumOfOrder α a s := by
  rcases hα.eq_or_lt with rfl | hα
  · unfold HasCesaroSumOfOrder
    rwa [show cesaroMeanOfOrder 0 a = seriesPartialSum a from funext (cesaroMeanOfOrder_zero a)]
  set A : ℕ → ℝ := fun k => (ascPochhammer ℝ k).eval (α + 1) / (k.factorial : ℝ) with hAdef
  have hApos : ∀ k, 0 < A k := fun k =>
    div_pos (ascPochhammer_pos k _ (by linarith)) (by positivity)
  have hAsucc : ∀ k, A (k + 1) = A k * ((α + 1 + k) / (k + 1)) := by
    intro k
    simp only [hAdef, ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul]
    push_cast
    field_simp
  have hAmono : Monotone A := by
    refine monotone_nat_of_le_succ fun k => ?_
    rw [hAsucc]
    refine le_mul_of_one_le_right (hApos k).le ?_
    rw [one_le_div (by positivity)]
    linarith
  set B : ℕ → ℝ := fun k => A k * (α / (α + k)) with hBdef
  have hBnn : ∀ k, 0 ≤ B k := fun k => mul_nonneg (hApos k).le (by positivity)
  have hBsum : ∀ m, ∑ k ∈ range (m + 1), B k = A m := by
    intro m
    induction m with
    | zero => simp [hBdef, hα.ne']
    | succ m ih =>
      rw [sum_range_succ, ih, hBdef]
      simp only
      rw [hAsucc]
      push_cast
      field_simp
      ring
  have hmean : ∀ n, cesaroMeanOfOrder α a n - s =
      ((A n)⁻¹ : ℂ) * ∑ k ∈ range (n + 1), (B k : ℂ) * (seriesPartialSum a (n - k) - s) := by
    intro n
    have hconv := sum_mul_sub_eq_sum_mul_partialSum (A := fun k => (A k : ℂ))
      (B := fun k => (B k : ℂ)) a (fun m => by exact_mod_cast hBsum m) n
    have hc : (((n.factorial : ℝ) / (ascPochhammer ℝ n).eval (α + 1) : ℝ) : ℂ) =
        ((A n)⁻¹ : ℂ) := by
      simp only [hAdef]; rw [← Complex.ofReal_inv, inv_div]
    have hsumB : ∑ k ∈ range (n + 1), (B k : ℂ) = A n := by exact_mod_cast hBsum n
    unfold cesaroMeanOfOrder
    rw [hc]
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hsumB]
    rw [← hconv]
    have : (A n : ℂ) ≠ 0 := by exact_mod_cast (hApos n).ne'
    field_simp
    simp [hAdef]
  rw [HasCesaroSumOfOrder, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp h (ε / 2) (half_pos hε)
  obtain ⟨C, hC⟩ := (h.sub_const s).norm.bddAbove_range
  have hC' : ∀ j, ‖seriesPartialSum a j - s‖ ≤ C := fun j => hC ⟨j, rfl⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC' 0)
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * K * C * α / ε)
  have hbad : K * (C * (α / (α + M))) < ε / 2 := by
    have hpos : 0 < α + M := by positivity
    rw [show K * (C * (α / (α + M))) = K * C * α / (α + M) by ring, div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hε] at hM
    nlinarith
  refine ⟨K + M, fun n hn => ?_⟩
  rw [dist_eq_norm, hmean n]
  have hterm : ∀ k ∈ range (n + 1), (A n)⁻¹ * (B k * ‖seriesPartialSum a (n - k) - s‖) ≤
      (A n)⁻¹ * B k * (ε / 2) + (if n - k < K then C * (α / (α + M)) else 0) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    split_ifs with hnk
    · -- a bad index: `k` is large, so `B_k / A_n` is small
      have hkM : M ≤ k := by omega
      have hBA : (A n)⁻¹ * B k ≤ α / (α + M) := by
        rw [hBdef]
        simp only
        rw [← mul_assoc]
        calc (A n)⁻¹ * A k * (α / (α + k)) ≤ 1 * (α / (α + M)) := by
              refine mul_le_mul ?_ ?_ (by positivity) zero_le_one
              · rw [inv_mul_le_one₀ (hApos n)]; exact hAmono hkn
              · exact div_le_div_of_nonneg_left hα.le (by positivity)
                  (by exact_mod_cast (by linarith [(Nat.cast_le (α := ℝ)).mpr hkM]))
          _ = α / (α + M) := one_mul _
      have := hC' (n - k)
      calc (A n)⁻¹ * (B k * ‖seriesPartialSum a (n - k) - s‖)
          = ((A n)⁻¹ * B k) * ‖seriesPartialSum a (n - k) - s‖ := by ring
        _ ≤ (α / (α + M)) * C := mul_le_mul hBA this (norm_nonneg _) (by positivity)
        _ ≤ (A n)⁻¹ * B k * (ε / 2) + C * (α / (α + M)) := by
          have : 0 ≤ (A n)⁻¹ * B k * (ε / 2) :=
            mul_nonneg (mul_nonneg (inv_nonneg.mpr (hApos n).le) (hBnn k)) (by positivity)
          linarith
    · have := hK (n - k) (by omega)
      rw [dist_eq_norm] at this
      rw [add_zero, mul_assoc ((A n)⁻¹) (B k)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this.le (hBnn k))
        (inv_nonneg.mpr (hApos n).le)
  have hcard : ((range (n + 1)).filter fun k => n - k < K).card ≤ K := by
    calc ((range (n + 1)).filter fun k => n - k < K).card
        ≤ (Finset.Ico (n + 1 - K) (n + 1)).card := by
          refine card_le_card fun k hk => ?_
          simp only [Finset.mem_filter, Finset.mem_range] at hk
          simp only [Finset.mem_Ico]
          omega
      _ = K := by simp; omega
  calc ‖((A n)⁻¹ : ℂ) * ∑ k ∈ range (n + 1), (B k : ℂ) * (seriesPartialSum a (n - k) - s)‖
      ≤ (A n)⁻¹ * ∑ k ∈ range (n + 1), B k * ‖seriesPartialSum a (n - k) - s‖ := by
        rw [norm_mul]
        have h1 : ‖((A n)⁻¹ : ℂ)‖ = (A n)⁻¹ := by
          rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_of_nonneg
            (inv_nonneg.mpr (hApos n).le)]
        rw [h1]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_))
          (inv_nonneg.mpr (hApos n).le)
        refine sum_congr rfl fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hBnn k)]
    _ = ∑ k ∈ range (n + 1), (A n)⁻¹ * (B k * ‖seriesPartialSum a (n - k) - s‖) := by
        rw [mul_sum]
    _ ≤ ∑ k ∈ range (n + 1), ((A n)⁻¹ * B k * (ε / 2) +
          (if n - k < K then C * (α / (α + M)) else 0)) := sum_le_sum hterm
    _ = ε / 2 + ((range (n + 1)).filter fun k => n - k < K).card * (C * (α / (α + M))) := by
        rw [sum_add_distrib, ← sum_mul, ← mul_sum, hBsum n, inv_mul_cancel₀ (hApos n).ne',
          one_mul, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    _ ≤ ε / 2 + K * (C * (α / (α + M))) := by
        gcongr
    _ < ε := by linarith

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
