/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Algebra.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Means (DLMF §1.2(iv))

Properties of the arithmetic, geometric, harmonic and weighted power means defined in
`DLMF/AlgebraicAnalytic/Algebra/Basic.lean`: the limits of `M(r)` as `r → ±∞` (1.2.23–1.2.24),
`M(1) = A` and `M(-1) = H` for equal weights (1.2.25), and `M(r) → G` as `r → 0` (1.2.26).

The limits 1.2.23–1.2.24 and 1.2.26 are proved for arbitrary positive weights `p_j` with
`∑ p_j = 1`; for 1.2.26 the limit is then the weighted geometric mean `∏ a_j^{p_j}`, which is
`G` for `p_j = 1/n` (stronger than DLMF, which states 1.2.26 for equal weights only). The maximum
and minimum of 1.2.23–1.2.24 are `⨆ j, a j` and `⨅ j, a j`.

The inequalities between the means (AM–GM and the power-mean inequality) are DLMF §1.7(iii)
and are not treated here; Mathlib has them as
`Real.geom_mean_le_arith_mean_weighted` and `Real.rpow_arith_mean_le_arith_mean_rpow`.
-/

@[expose] public noncomputable section

open Finset Filter Topology Real

namespace DLMF.AlgebraicAnalytic

variable {ι : Type*} [Fintype ι]

/-- DLMF 1.2.19: `1/H = (1/n)(1/a₁ + ⋯ + 1/aₙ)`. -/
@[dlmf 1.2.E19]
theorem inv_harmonicMean (a : ι → ℝ) :
    (harmonicMean a)⁻¹ = 1 / (Fintype.card ι : ℝ) * ∑ i, (a i)⁻¹ := by
  rw [harmonicMean, inv_inv, div_eq_inv_mul, one_div]

/-- The weighted power mean at `r > 0` is given by the formula 1.2.21. -/
theorem weightedPowerMean_of_pos (p a : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    weightedPowerMean p a r = (∑ i, p i * a i ^ r) ^ (1 / r) := by
  rw [weightedPowerMean, ite_eq_right hr.ne', ite_eq_right (fun h => absurd h.1 (not_lt.2 hr.le))]

/-- The weighted power mean at `r ≠ 0` of positive numbers is given by the formula 1.2.21. -/
theorem weightedPowerMean_of_ne_zero (p : ι → ℝ) {a : ι → ℝ} (ha : ∀ i, 0 < a i) {r : ℝ}
    (hr : r ≠ 0) : weightedPowerMean p a r = (∑ i, p i * a i ^ r) ^ (1 / r) := by
  have : ∏ i, a i ≠ 0 := prod_ne_zero_iff.2 fun i _ => (ha i).ne'
  rw [weightedPowerMean, ite_eq_right hr, ite_eq_right (fun h => this h.2)]

/-- Helper: `c ^ (1/r) → 1` as `r → ∞`, for `c > 0`. -/
lemma g1a_tendsto_rpow_one_div {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℝ => c ^ (1 / r)) atTop (𝓝 1) := by
  have h : Tendsto (fun r : ℝ => 1 / r) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hc' := (Real.continuousAt_const_rpow (a := c) (b := 0) hc.ne').tendsto
  rw [Real.rpow_zero] at hc'
  exact hc'.comp h

/-- Helper: for positive weights `w` and nonnegative `c` with a maximal entry `c i₀`,
`(∑ w_i c_i^r)^{1/r} → c i₀` as `r → ∞`. -/
theorem g1a_tendsto_sum_rpow_atTop {w c : ι → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ i, 0 ≤ c i)
    {i₀ : ι} (hi₀ : ∀ i, c i ≤ c i₀) :
    Tendsto (fun r : ℝ => (∑ i, w i * c i ^ r) ^ (1 / r)) atTop (𝓝 (c i₀)) := by
  set W := ∑ i, w i with hW
  have hWpos : 0 < W := lt_of_lt_of_le (hw i₀)
    (single_le_sum (fun i _ => (hw i).le) (mem_univ i₀))
  have hlow : Tendsto (fun r : ℝ => w i₀ ^ (1 / r) * c i₀) atTop (𝓝 (c i₀)) := by
    simpa using (g1a_tendsto_rpow_one_div (hw i₀)).mul_const (c i₀)
  have hupp : Tendsto (fun r : ℝ => W ^ (1 / r) * c i₀) atTop (𝓝 (c i₀)) := by
    simpa using (g1a_tendsto_rpow_one_div hWpos).mul_const (c i₀)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with r hr
    have h1 : w i₀ * c i₀ ^ r ≤ ∑ i, w i * c i ^ r :=
      single_le_sum (f := fun i => w i * c i ^ r)
        (fun i _ => mul_nonneg (hw i).le (rpow_nonneg (hc i) r)) (mem_univ i₀)
    have h2 := rpow_le_rpow (mul_nonneg (hw i₀).le (rpow_nonneg (hc i₀) r)) h1
      (one_div_nonneg.2 hr.le)
    rwa [mul_rpow (hw i₀).le (rpow_nonneg (hc i₀) r), one_div,
      rpow_rpow_inv (hc i₀) hr.ne', ← one_div] at h2
  · filter_upwards [eventually_gt_atTop 0] with r hr
    have h1 : ∑ i, w i * c i ^ r ≤ W * c i₀ ^ r := by
      rw [hW, sum_mul]
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (rpow_le_rpow (hc i) (hi₀ i) hr.le) (hw i).le
    have h2 := rpow_le_rpow (sum_nonneg fun i _ => mul_nonneg (hw i).le
      (rpow_nonneg (hc i) r)) h1 (one_div_nonneg.2 hr.le)
    rwa [mul_rpow hWpos.le (rpow_nonneg (hc i₀) r), one_div,
      rpow_rpow_inv (hc i₀) hr.ne', ← one_div] at h2

/-- DLMF 1.2.23: `M(r) → max(a₁, …, aₙ)` as `r → ∞`, for nonnegative `a_j` and positive weights
`p_j` (the normalization 1.2.20 is not needed). -/
@[dlmf 1.2.E23]
theorem tendsto_weightedPowerMean_atTop [Nonempty ι] {p a : ι → ℝ} (hp : ∀ i, 0 < p i)
    (ha : ∀ i, 0 ≤ a i) :
    Tendsto (weightedPowerMean p a) atTop (𝓝 (⨆ i, a i)) := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max a
  have hsup : (⨆ i, a i) = a i₀ :=
    le_antisymm (ciSup_le hi₀) (le_ciSup (Set.finite_range a).bddAbove i₀)
  rw [hsup]
  refine (g1a_tendsto_sum_rpow_atTop hp ha hi₀).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [weightedPowerMean_of_pos p a hr]

/-- DLMF 1.2.24: `M(r) → min(a₁, …, aₙ)` as `r → -∞`, for nonnegative `a_j` and positive
weights `p_j` (the normalization 1.2.20 is not needed). When some `a_j = 0` both sides are `0`
by the exception 1.2.22. -/
@[dlmf 1.2.E24]
theorem tendsto_weightedPowerMean_atBot [Nonempty ι] {p a : ι → ℝ} (hp : ∀ i, 0 < p i)
    (ha : ∀ i, 0 ≤ a i) :
    Tendsto (weightedPowerMean p a) atBot (𝓝 (⨅ i, a i)) := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min a
  have hinf : (⨅ i, a i) = a i₀ :=
    le_antisymm (ciInf_le (Set.finite_range a).bddBelow i₀) (le_ciInf hi₀)
  rw [hinf]
  by_cases h0 : ∏ i, a i = 0
  · obtain ⟨j, -, hj⟩ := prod_eq_zero_iff.1 h0
    have : a i₀ = 0 := le_antisymm (hj ▸ hi₀ j) (ha i₀)
    rw [this]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot 0] with r hr
    rw [weightedPowerMean, ite_eq_right hr.ne, ite_eq_left ⟨hr, h0⟩]
  have hpos : ∀ i, 0 < a i := fun i =>
    lt_of_le_of_ne (ha i) (Ne.symm fun h => h0 (prod_eq_zero (mem_univ i) h))
  have hmax : ∀ i, (a i)⁻¹ ≤ (a i₀)⁻¹ := fun i => inv_anti₀ (hpos i₀) (hi₀ i)
  have hT := (g1a_tendsto_sum_rpow_atTop hp (fun i => (inv_pos.2 (hpos i)).le) hmax).comp
    tendsto_neg_atBot_atTop
  have hT' := hT.inv₀ (inv_pos.2 (hpos i₀)).ne'
  rw [inv_inv] at hT'
  refine hT'.congr' ?_
  filter_upwards [eventually_lt_atBot 0] with r hr
  rw [weightedPowerMean_of_ne_zero p hpos hr.ne, Function.comp_apply]
  have hS : 0 ≤ ∑ i, p i * a i ^ r :=
    sum_nonneg fun i _ => mul_nonneg (hp i).le (rpow_nonneg (ha i) r)
  have hterm : ∀ i, (a i)⁻¹ ^ (-r) = a i ^ r := fun i => by
    rw [inv_rpow (ha i), rpow_neg (ha i), inv_inv]
  simp only [hterm]
  rw [show 1 / r = -(1 / -r) by rw [div_neg, neg_neg], rpow_neg hS]

/-- DLMF 1.2.25: for equal weights `p_j = 1/n`, `M(1) = A`. -/
@[dlmf 1.2.E25]
theorem weightedPowerMean_one (a : ι → ℝ) :
    weightedPowerMean (fun _ => 1 / (Fintype.card ι : ℝ)) a 1 = arithmeticMean a := by
  rw [weightedPowerMean_of_pos _ _ one_pos, arithmeticMean, div_one, rpow_one]
  simp only [rpow_one, ← mul_sum]
  ring

/-- DLMF 1.2.25: for equal weights `p_j = 1/n` and positive `a_j`, `M(-1) = H`. -/
@[dlmf 1.2.E25]
theorem weightedPowerMean_neg_one {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    weightedPowerMean (fun _ => 1 / (Fintype.card ι : ℝ)) a (-1) = harmonicMean a := by
  rw [weightedPowerMean_of_ne_zero _ ha (by norm_num), harmonicMean]
  simp only [rpow_neg_one, ← mul_sum]
  rw [show (1 : ℝ) / -1 = -1 by norm_num, rpow_neg_one]
  congr 1
  ring

/-- DLMF 1.2.26 (weighted form, stronger than DLMF): for positive `a_j` and positive weights with
`∑ p_j = 1` (1.2.20), `M(r) → ∏ a_j^{p_j}` as `r → 0`, `r ≠ 0`. -/
@[dlmf 1.2.E26]
theorem tendsto_weightedPowerMean_zero {p a : ι → ℝ} (hp : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i = 1) (ha : ∀ i, 0 < a i) :
    Tendsto (weightedPowerMean p a) (𝓝[≠] 0) (𝓝 (∏ i, a i ^ p i)) := by
  set S : ℝ → ℝ := fun r => ∑ i, p i * a i ^ r with hSdef
  have hS0 : S 0 = 1 := by simp [hSdef, hp1]
  have hSpos : ∀ r, 0 < S r := fun r => by
    have : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hp1
    exact sum_pos (fun i _ => mul_pos (hp i) (rpow_pos_of_pos (ha i) r)) univ_nonempty
  have hSd : HasDerivAt S (∑ i, p i * (a i ^ (0 : ℝ) * Real.log (a i))) 0 := by
    have := HasDerivAt.fun_sum (u := univ) (A := fun i (r : ℝ) => p i * a i ^ r)
      (A' := fun i => p i * (a i ^ (0 : ℝ) * Real.log (a i))) (x := (0 : ℝ))
      fun i _ => ((hasStrictDerivAt_const_rpow (ha i) 0).hasDerivAt).const_mul (p i)
    exact this
  have hφ := (hSd.log (by rw [hS0]; norm_num)).tendsto_slope_zero
  simp only [zero_add, hS0, Real.log_one, sub_zero, div_one, rpow_zero, one_mul,
    smul_eq_mul] at hφ
  have hexp := (Real.continuous_exp.tendsto _).comp hφ
  have hlim : Real.exp (∑ i, p i * Real.log (a i)) = ∏ i, a i ^ p i := by
    rw [Real.exp_sum]
    refine prod_congr rfl fun i _ => ?_
    rw [rpow_def_of_pos (ha i), mul_comm]
  rw [hlim] at hexp
  refine hexp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [Function.comp_apply, weightedPowerMean_of_ne_zero p ha hr, rpow_def_of_pos (hSpos r)]
  congr 1
  simp [hSdef]
  ring

/-- DLMF 1.2.26: for equal weights `p_j = 1/n` and positive `a_j`, `M(r) → G` as `r → 0`. -/
@[dlmf 1.2.E26]
theorem tendsto_weightedPowerMean_zero_geometricMean [Nonempty ι] {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) :
    Tendsto (weightedPowerMean (fun _ => 1 / (Fintype.card ι : ℝ)) a) (𝓝[≠] 0)
      (𝓝 (geometricMean a)) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := tendsto_weightedPowerMean_zero (p := fun _ => 1 / (Fintype.card ι : ℝ))
    (fun _ => by positivity) (by simp [hn]) ha
  rwa [geometricMean, ← Real.finsetProd_rpow _ _ fun i _ => (ha i).le]

end DLMF.AlgebraicAnalytic
