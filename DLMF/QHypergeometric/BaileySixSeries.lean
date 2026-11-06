/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.BaileySixShift

/-!
# Summation and analytic continuation of the six-psi-six kernel

The negative tail terminates at geometric parameter nodes. The shifted sum is a
fully cleared Rogers six-phi-five sum, and the nodes accumulate at zero inside the
normal-convergence disk of the bilateral kernel.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.BaileySixSummation

/-- Summing the geometric-node shift gives the fully cleared Rogers product. -/
lemma tsum_term_pow_eq_shifted {a b c d q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (ha1 : a ≠ 1) (hbcd : b * c * d ≠ 0)
    (hL : QDenominatorRegular [a * q / b, a * q / c, a * q / d] q)
    (hU : ∀ u ∈ [b, c, d], ∀ j : ℕ, u ≠ q ^ (j + 1))
    (m : ℕ) (hm : ∀ j : ℕ, a / q ^ m ≠ q ^ (j + 1))
    (hz : ‖shiftArgument a b c d q m‖ < 1) :
    (∑' n : ℤ, term a b c d q (q ^ m / a) n) = shiftFactor a b c d q m *
      SixPhiFiveCleared.productSide (b / q ^ m) (c / q ^ m) (d / q ^ m) q
        (a / q ^ (2 * m)) := by
  have hb := left_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hc := right_ne_zero_of_mul (left_ne_zero_of_mul hbcd)
  have hd := right_ne_zero_of_mul hbcd
  have hqm := pow_ne_zero m hq0
  have hvanish : ∀ n ∉ Set.range (fun k : ℕ => (k : ℤ) - m),
      term a b c d q (q ^ m / a) n = 0 := by
    intro n hn
    apply term_pow_eq_zero hq0 ha m
    by_contra hge
    push Not at hge
    exact hn ⟨(n + m).toNat, by simp only; omega⟩
  have hinj : Function.Injective (fun k : ℕ => (k : ℤ) - m) := fun k l h => by
    simpa using h
  rw [← hinj.tsum_eq (by
    intro n hn
    by_contra he
    exact hn (hvanish n he))]
  simp_rw [term_pow_shift hq0 hq ha ha1 hbcd hL hU m hm]
  rw [tsum_mul_left]
  have hshift : (b / q ^ m) * (c / q ^ m) * (d / q ^ m) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (div_ne_zero hb hqm) (div_ne_zero hc hqm)) (div_ne_zero hd hqm)
  have hz' : ‖(a / q ^ (2 * m)) * q‖ <
      ‖(b / q ^ m) * (c / q ^ m) * (d / q ^ m)‖ := by
    have H := hz
    rw [← shifted_argument (a := a) hq0 hbcd m, norm_div,
      div_lt_one (norm_pos_iff.mpr hshift)] at H
    exact H
  rw [SixPhiFiveCleared.tsum_term_eq_productSide hq0 hq hz']

/-- The shifted upper parameter is eventually regular and the node arguments tend to zero. -/
lemma eventually_node_conditions {a b c d q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) :
    ∀ᶠ m : ℕ in atTop, (∀ j : ℕ, a / q ^ m ≠ q ^ (j + 1)) ∧
      ‖shiftArgument a b c d q m‖ < 1 := by
  have ht := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  have hnorm : Tendsto (fun m : ℕ => ‖q ^ m‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using ht.norm
  have hz : Tendsto (shiftArgument a b c d q) atTop (𝓝 (0 : ℂ)) := by
    simpa only [scale_mul_pow_div ha hq0, zero_div, mul_zero] using
      (ht.div_const a).const_mul (scale a b c d q)
  have hzNorm : Tendsto (fun m : ℕ => ‖shiftArgument a b c d q m‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using hz.norm
  filter_upwards [hnorm.eventually_lt tendsto_const_nhds (norm_pos_iff.mpr ha),
    hzNorm.eventually_lt tendsto_const_nhds one_pos] with m hma hzm
  refine ⟨?_, hzm⟩
  intro j he
  have hqm : 0 < ‖q ^ m‖ := norm_pos_iff.mpr (pow_ne_zero m hq0)
  have hlarge : 1 < ‖a / q ^ m‖ := by
    rw [norm_div, one_lt_div hqm]
    exact hma
  rw [he, norm_pow] at hlarge
  exact (not_lt.mpr (pow_le_one₀ (norm_nonneg q) hq.le)) hlarge

/-- Agreement at the geometric parameter nodes determines the cleared bilateral sum. -/
lemma tsum_term_eq_of_eventually_pow {a b c d q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : a ≠ 0) (hbcd : b * c * d ≠ 0)
    (hpow : ∀ᶠ m : ℕ in atTop, (∑' n : ℤ, term a b c d q (q ^ m / a) n) =
      productSide a b c d q (q ^ m / a))
    (hx : ‖x‖ < ‖scale a b c d q‖⁻¹) :
    (∑' n : ℤ, term a b c d q x n) = productSide a b c d q x := by
  have hT : 0 < ‖scale a b c d q‖ :=
    norm_pos_iff.mpr (div_ne_zero (mul_ne_zero hq0 (pow_ne_zero 2 ha)) hbcd)
  let U := Metric.ball (0 : ℂ) ‖scale a b c d q‖⁻¹
  have hF : AnalyticOnNhd ℂ (fun x => ∑' n : ℤ, term a b c d q x n) U :=
    analyticOnNhd_tsum_term hq0 hq ha hbcd
  have hG : AnalyticOnNhd ℂ (productSide a b c d q) U := fun x _ =>
    (differentiable_productSide hq a b c d).analyticAt x
  have h0 : (0 : ℂ) ∈ U := Metric.mem_ball_self (inv_pos.mpr hT)
  have ht : Tendsto (fun m : ℕ => q ^ m / a) atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun m =>
      div_ne_zero (pow_ne_zero m hq0) ha⟩
    simpa only [zero_div] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).div_const a
  have hfreq : ∃ᶠ y in 𝓝[≠] (0 : ℂ), (∑' n : ℤ, term a b c d q y n) =
      productSide a b c d q y := ht.frequently hpow.frequently
  exact (hF.eqOn_of_preconnected_of_frequently_eq hG
    (convex_ball (0 : ℂ) _).isPreconnected h0 hfreq) (by simpa only [U, mem_ball_zero_iff] using hx)

end DLMF.QHypergeometric.BaileySixSummation
