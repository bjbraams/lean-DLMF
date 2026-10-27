/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Riemann
public import DLMF.Zeta.Reflection
public import DLMF.BernoulliEuler.IntegralsSums
public import DLMF.Polylog.Dilog
public import DLMF.Hypergeometric.Clausen
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The Riemann zeta function at integer arguments (DLMF §25.6)

Mathlib proves `ζ(0) = -1/2`, `ζ(2) = π²/6` (25.6.1), Euler's `ζ(2n)` formula (25.6.2), `ζ(-n)`
(25.6.3, for all `n ≥ 0`), the trivial zeros (25.6.4) and `ζ'(0) = -½ ln(2π)` (25.6.11); the
pointers are in `DLMF.Core.UpstreamElementary` and `DLMF.Zeta.MathlibCoverage`. This file proves
`ζ(4)`, `ζ(6)` and the derivative values 25.6.13–25.6.14 at the trivial zeros and at negative odd
integers (from the derivative reflection formula 25.4.5) and acquires the remaining formulas.

`ζ^{(k)}` is `iteratedDeriv k riemannZeta`, `Γ^{(r)}` is `iteratedDeriv r Gamma`, `ψ` is
`Complex.digamma`, `γ₁` is `stieltjesConstant 1` (25.2.5) and `c` is `reflectionConst` (25.4.6).
-/

@[expose] public noncomputable section

open Complex Filter Topology MeasureTheory Set Finset
open scoped Real Nat

namespace DLMF.Zeta

/-! ### §25.6(i) Function values -/

/-- DLMF 25.6.1: `ζ(4) = π⁴/90` (from Mathlib's `riemannZeta_two_mul_nat`). -/
@[dlmf 25.6.E1]
theorem riemannZeta_four : riemannZeta 4 = π ^ 4 / 90 := by
  have h := riemannZeta_two_mul_nat (k := 2) (by norm_num)
  have hb : bernoulli 4 = -1 / 30 := by decide +kernel
  norm_num [hb, Nat.factorial] at h
  rw [h]; ring

/-- DLMF 25.6.1: `ζ(6) = π⁶/945` (from Mathlib's `riemannZeta_two_mul_nat`). -/
@[dlmf 25.6.E1]
theorem riemannZeta_six : riemannZeta 6 = π ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  have hb : bernoulli 6 = 1 / 42 := by decide +kernel
  norm_num [hb, Nat.factorial] at h
  rw [h]; ring

/-- DLMF 25.6.5: for `k ≥ 1`,
`ζ(k+1) = (1/k!) ∑_{n₁,…,n_k ≥ 1} 1/(n₁⋯n_k (n₁ + ⋯ + n_k))`, stated as the (absolutely
convergent) sum of the `k`-fold series being `k! ζ(k+1)`; the summation variables are
`nᵢ + 1`, `nᵢ : ℕ`. -/
@[dlmf 25.6.E5]
theorem hasSum_multiple_sum_riemannZeta {k : ℕ} (hk : 1 ≤ k) :
    HasSum (fun n : Fin k → ℕ =>
        (1 : ℂ) / ((∏ i, ((n i : ℂ) + 1)) * ∑ i, ((n i : ℂ) + 1)))
      (k ! * riemannZeta (k + 1)) := by
  sorry

/-- `sin(2πnt) cot(πt) = ∑_{j<n} (cos(2π(j+1)t) + cos(2πjt))` where `sin(πt) ≠ 0`. -/
lemma r25a_sin_mul_cot {t : ℝ} (ht : Real.sin (π * t) ≠ 0) (n : ℕ) :
    Real.sin (2 * π * n * t) * Real.cot (π * t) =
      ∑ j ∈ range n, (Real.cos (2 * π * (j + 1) * t) + Real.cos (2 * π * j * t)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← ih, Real.cot_eq_cos_div_sin]
    push_cast
    set A := 2 * π * n * t
    set B := π * t
    rw [show 2 * π * ((n : ℝ) + 1) * t = A + 2 * B by simp only [A, B]; ring]
    rw [Real.sin_add, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul]
    field_simp
    linear_combination (2 * Real.cos B * Real.sin A) * Real.sin_sq_add_cos_sq B

/-- `|sin(2πnt) cot(πt)| ≤ 2n`. -/
lemma r25a_abs_sin_mul_cot_le (t : ℝ) (n : ℕ) :
    |Real.sin (2 * π * n * t) * Real.cot (π * t)| ≤ 2 * n := by
  by_cases ht : Real.sin (π * t) = 0
  · rw [Real.cot_eq_cos_div_sin, ht, div_zero, mul_zero, abs_zero]; positivity
  rw [r25a_sin_mul_cot ht]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ range n, |Real.cos (2 * π * (j + 1) * t) + Real.cos (2 * π * j * t)|
      ≤ ∑ _j ∈ range n, (2 : ℝ) := sum_le_sum fun j _ => (abs_add_le _ _).trans (by
        linarith [Real.abs_cos_le_one (2 * π * (j + 1) * t), Real.abs_cos_le_one (2 * π * j * t)])
    _ = 2 * n := by simp; ring

/-- `∫₀¹ cos(2πjt) dt = 0` for `j ≥ 1`. -/
lemma r25a_integral_cos {j : ℕ} (hj : j ≠ 0) :
    ∫ t in (0 : ℝ)..1, Real.cos (2 * π * j * t) = 0 := by
  have hc : (2 * π * j : ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => Real.sin (2 * π * j * t) / (2 * π * j)) (fun t _ => ?_)
    ((by fun_prop : Continuous fun t : ℝ => Real.cos (2 * π * j * t)).intervalIntegrable 0 1)]
  · rw [mul_one, show 2 * π * (j : ℝ) = ((2 * j : ℕ) : ℝ) * π by push_cast; ring,
      Real.sin_nat_mul_pi]
    simp
  · have := ((hasDerivAt_id t).const_mul (2 * π * j)).sin.div_const (2 * π * j)
    convert this using 1
    · rfl
    · rw [id_eq, mul_one, mul_div_assoc, div_self hc, mul_one]

open scoped Interval in
/-- `∫₀¹ sin(2πnt) cot(πt) dt = 1` for `n ≥ 1`. -/
lemma r25a_integral_sin_mul_cot {n : ℕ} (hn : n ≠ 0) :
    ∫ t in (0 : ℝ)..1, Real.sin (2 * π * n * t) * Real.cot (π * t) = 1 := by
  have hae : ∀ᵐ t : ℝ ∂volume, t ∈ Ι (0 : ℝ) 1 →
      Real.sin (2 * π * n * t) * Real.cot (π * t) =
      ∑ j ∈ range n, (Real.cos (2 * π * (j + 1) * t) + Real.cos (2 * π * j * t)) := by
    have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by rw [ae_iff]; simp
    filter_upwards [hne1] with t ht1 ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    refine r25a_sin_mul_cot ?_ n
    exact (Real.sin_pos_of_pos_of_lt_pi (by nlinarith [ht.1, Real.pi_pos])
      (by nlinarith [lt_of_le_of_ne ht.2 ht1, Real.pi_pos])).ne'
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_finsetSum]
  · have : ∀ j ∈ range n, ∫ t in (0 : ℝ)..1,
        (Real.cos (2 * π * (j + 1) * t) + Real.cos (2 * π * j * t)) = if j = 0 then 1 else 0 := by
      intro j _
      rw [intervalIntegral.integral_add, show (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) by push_cast; ring,
        r25a_integral_cos (by omega)]
      · split_ifs with h
        · subst h; simp
        · rw [r25a_integral_cos h]; simp
      all_goals exact (by fun_prop : Continuous fun t : ℝ => Real.cos _).intervalIntegrable 0 1
    rw [sum_congr rfl this, sum_ite_eq' (range n) 0]
    simp [Nat.pos_of_ne_zero hn]
  · intro j _
    exact (by fun_prop : Continuous fun t : ℝ =>
      Real.cos (2 * π * ((j : ℝ) + 1) * t) + Real.cos (2 * π * j * t)).intervalIntegrable 0 1

/-- DLMF 25.6.6: for `k ≥ 1`,
`ζ(2k+1) = ((-1)^{k+1} (2π)^{2k+1} / (2(2k+1)!)) ∫₀¹ B_{2k+1}(t) cot(πt) dt`; the integrand is
bounded (`B_{2k+1}` vanishes at `0` and `1`). -/
@[dlmf 25.6.E6]
theorem riemannZeta_two_mul_add_one_eq_integral {k : ℕ} (hk : 1 ≤ k) :
    IntervalIntegrable (fun t : ℝ => bernoulliFun (2 * k + 1) t * Real.cot (π * t))
        volume 0 1 ∧
      riemannZeta (2 * k + 1) = (((-1) ^ (k + 1) * (2 * π) ^ (2 * k + 1) /
        (2 * (2 * k + 1)!) * ∫ t in (0 : ℝ)..1,
          bernoulliFun (2 * k + 1) t * Real.cot (π * t) : ℝ) : ℂ) := by
  set c : ℝ := (-1) ^ (k + 1) * (2 * π) ^ (2 * k + 1) / 2 / (2 * k + 1)! with hc
  have hc0 : c ≠ 0 := by
    simp only [hc]
    have : ((2 * k + 1)! : ℝ) ≠ 0 := by positivity
    have : (2 * π) ^ (2 * k + 1) ≠ 0 := by positivity
    simp_all
  set F : ℕ → ℝ → ℝ := fun n t =>
    1 / (n : ℝ) ^ (2 * k + 1) * Real.sin (2 * π * n * t) * Real.cot (π * t) with hF
  set bound : ℕ → ℝ → ℝ := fun n _ => 2 * (1 / (n : ℝ) ^ (2 * k)) with hbound
  have hlim : ∀ t ∈ Icc (0 : ℝ) 1, HasSum (fun n => F n t)
      (c * (bernoulliFun (2 * k + 1) t * Real.cot (π * t))) := by
    intro t ht
    have := (hasSum_one_div_nat_pow_mul_sin (by omega : k ≠ 0) ht).mul_right (Real.cot (π * t))
    convert this using 1
    simp only [hc, bernoulliFun]; ring
  have hFb : ∀ n t, ‖F n t‖ ≤ bound n t := by
    intro n t
    simp only [hF, hbound, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [mul_assoc, abs_mul, abs_of_pos (by positivity)]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc 1 / (n : ℝ) ^ (2 * k + 1) * |Real.sin (2 * π * n * t) * Real.cot (π * t)|
        ≤ 1 / (n : ℝ) ^ (2 * k + 1) * (2 * n) :=
          mul_le_mul_of_nonneg_left (r25a_abs_sin_mul_cot_le t n) (by positivity)
      _ = 2 * (1 / (n : ℝ) ^ (2 * k)) := by rw [pow_succ]; field_simp
  have hbs : Summable (fun n : ℕ => 2 * (1 / (n : ℝ) ^ (2 * k))) :=
    (Real.summable_one_div_nat_pow.mpr (by omega)).mul_left 2
  have hmeasF : ∀ n, Measurable (F n) := fun n => by
    simp only [hF, Real.cot_eq_cos_div_sin]; fun_prop
  have hmeasf : Measurable (fun t => bernoulliFun (2 * k + 1) t * Real.cot (π * t)) := by
    have : Continuous (bernoulliFun (2 * k + 1)) := by
      unfold bernoulliFun; exact Polynomial.continuous _
    simp only [Real.cot_eq_cos_div_sin]
    exact this.measurable.mul (by fun_prop)
  -- integrability: `|f| ≤ (∑ bound)/|c|` on `[0,1]`
  have hint : IntervalIntegrable (fun t : ℝ => bernoulliFun (2 * k + 1) t * Real.cot (π * t))
      volume 0 1 := by
    refine (intervalIntegrable_const (c := (∑' n : ℕ, 2 * (1 / (n : ℝ) ^ (2 * k))) / |c|)).mono_fun'
      hmeasf.aestronglyMeasurable ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine ae_of_all _ fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have h := hlim t ⟨ht.1.le, ht.2⟩
    have hle : ‖c * (bernoulliFun (2 * k + 1) t * Real.cot (π * t))‖ ≤
        ∑' n : ℕ, 2 * (1 / (n : ℝ) ^ (2 * k)) := by
      rw [← h.tsum_eq]
      have hs : Summable (fun n => ‖F n t‖) :=
        hbs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hFb n t)
      exact (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum (fun n => hFb n t) hs hbs)
    rw [norm_mul, Real.norm_eq_abs] at hle
    rw [le_div_iff₀ (abs_pos.mpr hc0), mul_comm]
    exact hle
  refine ⟨hint, ?_⟩
  have hI := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := 1) bound (fun n => (hmeasF n).aestronglyMeasurable)
    (fun n => ae_of_all _ fun t _ => hFb n t) (ae_of_all _ fun _ _ => hbs)
    (by simp only [hbound]; exact intervalIntegrable_const)
    (ae_of_all _ fun t ht => by
      rw [Set.uIoc_of_le zero_le_one] at ht; exact hlim t ⟨ht.1.le, ht.2⟩)
  have hint_n : ∀ n : ℕ, ∫ t in (0 : ℝ)..1, F n t = 1 / (n : ℝ) ^ (2 * k + 1) := by
    intro n
    have e : (fun t => F n t) = fun t => 1 / (n : ℝ) ^ (2 * k + 1) *
        (Real.sin (2 * π * n * t) * Real.cot (π * t)) := by
      funext t; simp only [hF]; ring
    rw [e, intervalIntegral.integral_const_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [r25a_integral_sin_mul_cot hn.ne', mul_one]
  simp only [hint_n, intervalIntegral.integral_const_mul] at hI
  have hz := zeta_nat_eq_tsum_of_gt_one (k := 2 * k + 1) (by omega)
  push_cast at hz
  rw [hz]
  have hC := (Complex.ofRealCLM.hasSum hI)
  simp only [ofRealCLM_apply] at hC
  push_cast at hC
  rw [hC.tsum_eq]
  simp only [hc]
  push_cast
  ring

open DLMF.Polylog in
/-- The dilogarithm kernel `-ln(1-x)/x` is integrable on `[0, 1]`. -/
lemma r25a_intervalIntegrable_dilogKernel :
    IntervalIntegrable dilogKernel volume 0 1 := by
  refine intervalIntegral.intervalIntegrable_deriv_of_nonneg
      (g := fun t : ℝ => (polylogSeries 2 t).re)
    (continuousOn_re_polylogSeries_two.mono (by
      rw [Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc (by norm_num) le_rfl)) ?_ ?_
  · intro t ht
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at ht
    exact hasDerivAt_re_polylogSeries_two (abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩)
  · intro t ht
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at ht
    exact dilogKernel_nonneg (abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩)

open DLMF.Polylog in
/-- `∫₀¹ dy/(1 - xy) = -ln(1-x)/x` for `0 ≤ x < 1` (the kernel `dilogKernel`). -/
lemma r25a_inner_integral {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∫ y in (0 : ℝ)..1, 1 / (1 - x * y) = dilogKernel x := by
  rcases eq_or_lt_of_le hx0 with rfl | hx
  · simp [dilogKernel_zero]
  rw [dilogKernel_of_ne hx.ne']
  have hpos : ∀ y ∈ uIcc (0 : ℝ) 1, 0 < 1 - x * y := fun y hy => by
    rw [Set.uIcc_of_le zero_le_one] at hy
    nlinarith [hy.1, hy.2]
  have hc : ContinuousOn (fun y : ℝ => 1 / (1 - x * y)) (uIcc 0 1) :=
    continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      fun y hy => (hpos y hy).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => -Real.log (1 - x * y) / x) (fun y hy => ?_)
    (hc.intervalIntegrable)]
  · simp
  · have h := (((hasDerivAt_id y).const_mul x).const_sub 1).log (hpos y hy).ne'
    have h2 := h.neg.div_const x
    convert h2 using 1
    · funext y; simp [neg_div]
    · simp only [id]
      field_simp

open DLMF.Polylog in
/-- DLMF 25.6.7: `ζ(2) = ∫₀¹ ∫₀¹ dx dy/(1 - xy)`; the integrand is integrable on the unit
square (it is singular only at `(1, 1)`). -/
@[dlmf 25.6.E7]
theorem riemannZeta_two_eq_double_integral :
    IntegrableOn (fun p : ℝ × ℝ => 1 / (1 - p.1 * p.2)) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
      riemannZeta 2 = ((∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, 1 / (1 - x * y) : ℝ) : ℂ) := by
  have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
    rw [ae_iff]; simp
  have hout : ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, 1 / (1 - x * y) =
      ∫ x in (0 : ℝ)..1, dilogKernel x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne1] with x hx hmem
    rw [Set.uIoc_of_le zero_le_one] at hmem
    exact r25a_inner_integral hmem.1.le (lt_of_le_of_ne hmem.2 hx)
  refine ⟨?_, ?_⟩
  · have hmeas : Measurable (fun p : ℝ × ℝ => 1 / (1 - p.1 * p.2)) := by fun_prop
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict,
      integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hne1] with x hx hmem
      have hx1 : x < 1 := lt_of_le_of_ne hmem.2 hx
      refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
      exact continuousOn_const.div (continuousOn_const.sub
        (continuousOn_const.mul continuousOn_id)) fun y hy => by nlinarith [hy.1, hy.2, hmem.1]
    · have hk := r25a_intervalIntegrable_dilogKernel
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at hk
      refine hk.congr_fun_ae ?_
      rw [EventuallyEq, ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hne1] with x hx hmem
      have hx1 : x < 1 := lt_of_le_of_ne hmem.2 hx
      rw [← r25a_inner_integral hmem.1 hx1, intervalIntegral.integral_of_le zero_le_one,
        ← integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Icc fun y hy => ?_
      have : 0 < 1 - x * y := by nlinarith [hy.1, hy.2, hmem.1]
      simp [Real.norm_eq_abs, abs_of_pos this]
  · rw [hout, ← Real.dilog, Real.dilog_one, riemannZeta_two]
    push_cast; ring

/-- DLMF 25.6.8: `ζ(2) = 3 ∑_{k≥1} 1/(k² binom(2k, k))`. Proved from Euler's `arcsin²` series
at `x = 1/2` (`DLMF.Hypergeometric.hasSum_recip_sq_mul_centralBinom`). -/
@[dlmf 25.6.E8]
theorem hasSum_riemannZeta_two_central_binom :
    HasSum (fun k : ℕ => (3 : ℂ) / (((k : ℂ) + 1) ^ 2 * ((2 * k + 2).choose (k + 1) : ℂ)))
      (riemannZeta 2) := by
  have h := (hasSum_nat_add_iff' 1).mpr DLMF.Hypergeometric.hasSum_recip_sq_mul_centralBinom
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_pow two_ne_zero, zero_mul,
    div_zero, sub_zero] at h
  have h3 := (Complex.ofRealCLM.hasSum h).mul_left 3
  rw [riemannZeta_two]
  convert h3 using 1
  · funext k
    simp only [ofRealCLM_apply]
    push_cast
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    ring
  · simp only [ofRealCLM_apply]; push_cast; ring

/-- DLMF 25.6.9: `ζ(3) = (5/2) ∑_{k≥1} (-1)^{k-1}/(k³ binom(2k, k))`. -/
@[dlmf 25.6.E9]
theorem hasSum_riemannZeta_three_central_binom :
    HasSum (fun k : ℕ => (5 / 2 : ℂ) * (-1) ^ k /
        (((k : ℂ) + 1) ^ 3 * ((2 * k + 2).choose (k + 1) : ℂ))) (riemannZeta 3) := by
  sorry

/-- DLMF 25.6.10: `ζ(4) = (36/17) ∑_{k≥1} 1/(k⁴ binom(2k, k))`. -/
@[dlmf 25.6.E10]
theorem hasSum_riemannZeta_four_central_binom :
    HasSum (fun k : ℕ => (36 / 17 : ℂ) /
        (((k : ℂ) + 1) ^ 4 * ((2 * k + 2).choose (k + 1) : ℂ))) (riemannZeta 4) := by
  sorry

/-! ### §25.6(ii) Derivative values -/

/-- DLMF 25.6.12: `ζ''(0) = -½ (ln 2π)² + ½ γ² - π²/24 + γ₁`, with the Stieltjes constant `γ₁`
of 25.2.5. -/
@[dlmf 25.6.E12]
theorem iteratedDeriv_two_riemannZeta_zero :
    iteratedDeriv 2 riemannZeta 0 = -(1 / 2) * (Real.log (2 * π) : ℂ) ^ 2 +
      1 / 2 * (Real.eulerMascheroniConstant : ℂ) ^ 2 - π ^ 2 / 24 + stieltjesConstant 1 := by
  sorry

private lemma z25a_cos_nat_mul_pi (n : ℕ) : cos (n * π) = (-1) ^ n := by
  rw [← ofReal_natCast, ← ofReal_mul, ← ofReal_cos, Real.cos_nat_mul_pi]
  push_cast; rfl

/-- DLMF 25.6.13: for `n ≥ 1` and `k ≥ 0`,
`(-1)^k ζ^{(k)}(-2n) = (2(-1)ⁿ/(2π)^{2n+1}) ∑_{m=0}^{k} ∑_{r=0}^{m} binom(k,m) binom(m,r)
  Im(c^{k-m}) Γ^{(r)}(2n+1) ζ^{(m-r)}(2n+1)`.
Proved from 25.4.5 at `s = 2n+1`. -/
@[dlmf 25.6.E13]
theorem iteratedDeriv_riemannZeta_neg_two_mul {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (-1 : ℂ) ^ k * iteratedDeriv k riemannZeta (-2 * n) =
      2 * (-1) ^ n / (2 * π) ^ (2 * n + 1) * ∑ m ∈ range (k + 1), ∑ r ∈ range (m + 1),
        (k.choose m : ℂ) * (m.choose r : ℂ) * ((reflectionConst ^ (k - m)).im : ℂ) *
          iteratedDeriv r Gamma (2 * n + 1) * iteratedDeriv (m - r) riemannZeta (2 * n + 1) := by
  have hs : ∀ j : ℕ, (2 * n + 1 : ℂ) ≠ -j := by
    intro j h
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hs1 : (2 * n + 1 : ℂ) ≠ 1 := by
    intro h
    have : (n : ℂ) = 0 := by linear_combination h / 2
    exact absurd (by exact_mod_cast this : n = 0) (by omega)
  have h := iteratedDeriv_riemannZeta_one_sub hs hs1 k
  rw [show (1 : ℂ) - (2 * n + 1) = -2 * n by ring] at h
  have hcos : cos (π * (2 * n + 1) / 2) = 0 := by
    rw [show (π : ℂ) * (2 * n + 1) / 2 = n * π + π / 2 by ring, cos_add_pi_div_two,
      sin_nat_mul_pi, neg_zero]
  have hsin : sin (π * (2 * n + 1) / 2) = (-1) ^ n := by
    rw [show (π : ℂ) * (2 * n + 1) / 2 = n * π + π / 2 by ring, sin_add_pi_div_two,
      z25a_cos_nat_mul_pi]
  have hpow : (2 * (π : ℂ)) ^ (2 * (n : ℂ) + 1) = (2 * π) ^ (2 * n + 1) := by
    rw [show (2 * (n : ℂ) + 1) = ((2 * n + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]
  rw [h, hcos, hsin, hpow, mul_sum, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  ring

/-- DLMF 25.6.14: for `n ≥ 1` and `k ≥ 0`,
`(-1)^k ζ^{(k)}(1-2n) = (2(-1)ⁿ/(2π)^{2n}) ∑_{m=0}^{k} ∑_{r=0}^{m} binom(k,m) binom(m,r)
  Re(c^{k-m}) Γ^{(r)}(2n) ζ^{(m-r)}(2n)`.
Proved from 25.4.5 at `s = 2n`. -/
@[dlmf 25.6.E14]
theorem iteratedDeriv_riemannZeta_one_sub_two_mul {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (-1 : ℂ) ^ k * iteratedDeriv k riemannZeta (1 - 2 * n) =
      2 * (-1) ^ n / (2 * π) ^ (2 * n) * ∑ m ∈ range (k + 1), ∑ r ∈ range (m + 1),
        (k.choose m : ℂ) * (m.choose r : ℂ) * ((reflectionConst ^ (k - m)).re : ℂ) *
          iteratedDeriv r Gamma (2 * n) * iteratedDeriv (m - r) riemannZeta (2 * n) := by
  have hs : ∀ j : ℕ, (2 * n : ℂ) ≠ -j := by
    intro j h
    have := congrArg re h
    simp at this
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hs1 : (2 * n : ℂ) ≠ 1 := by
    intro h
    have := congrArg re h
    simp at this
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h := iteratedDeriv_riemannZeta_one_sub hs hs1 k
  have hcos : cos (π * (2 * n) / 2) = (-1) ^ n := by
    rw [show (π : ℂ) * (2 * n) / 2 = n * π by ring, z25a_cos_nat_mul_pi]
  have hsin : sin (π * (2 * n) / 2) = 0 := by
    rw [show (π : ℂ) * (2 * n) / 2 = n * π by ring, sin_nat_mul_pi]
  have hpow : (2 * (π : ℂ)) ^ (2 * (n : ℂ)) = (2 * π) ^ (2 * n) := by
    rw [show (2 * (n : ℂ)) = ((2 * n : ℕ) : ℂ) by push_cast; ring, cpow_natCast]
  rw [h, hcos, hsin, hpow, mul_sum, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  ring

/-- DLMF 25.6.15: for `n ≥ 1`,
`ζ'(2n) = ((-1)^{n+1} (2π)^{2n}/(2(2n)!)) (2n ζ'(1-2n) - (ψ(2n) - ln(2π)) B_{2n})`. -/
@[dlmf 25.6.E15]
theorem deriv_riemannZeta_two_mul {n : ℕ} (hn : 1 ≤ n) :
    deriv riemannZeta (2 * n) = (-1) ^ (n + 1) * (2 * π) ^ (2 * n) / (2 * (2 * n)!) *
      (2 * n * deriv riemannZeta (1 - 2 * n) -
        (digamma (2 * n) - Real.log (2 * π)) * bernoulli (2 * n)) := by
  have h := iteratedDeriv_riemannZeta_one_sub_two_mul hn 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_self,
    Nat.choose_zero_right, Nat.cast_one, one_mul, pow_one, pow_zero,
    Nat.sub_self, Nat.sub_zero, iteratedDeriv_zero, iteratedDeriv_one, one_re, ofReal_one,
    mul_one] at h
  have hc : (reflectionConst.re : ℂ) = -(Real.log (2 * π) : ℂ) := by
    simp [reflectionConst]
  rw [hc] at h
  have hG : Gamma (2 * n) = ((2 * n - 1 : ℕ) ! : ℂ) := by
    rw [← Gamma_nat_eq_factorial]; congr 1; push_cast [show 1 ≤ 2 * n by omega]; ring
  have hGne : Gamma (2 * n) ≠ 0 := by rw [hG]; exact_mod_cast (Nat.factorial_pos _).ne'
  have hψ : deriv Gamma (2 * n) = digamma (2 * n) * Gamma (2 * n) := by
    rw [digamma_def, logDeriv_apply]; field_simp
  have hF : ((2 * n)! : ℂ) = 2 * n * ((2 * n - 1 : ℕ) ! : ℂ) := by
    rw [show 2 * n = (2 * n - 1) + 1 by omega, Nat.factorial_succ]
    push_cast [show 1 ≤ 2 * n by omega]; ring
  have hz := riemannZeta_two_mul_nat (k := n) (by omega)
  have hP : (2 * (π : ℂ)) ^ (2 * n) = 2 * (2 : ℂ) ^ (2 * n - 1) * (π : ℂ) ^ (2 * n) := by
    rw [mul_pow, ← pow_succ', show 2 * n - 1 + 1 = 2 * n by omega]
  have hPne : (2 * (π : ℂ)) ^ (2 * n) ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero])
  have he : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hψ, hG] at h
  rw [hG] at hGne
  set G : ℂ := ((2 * n - 1 : ℕ) ! : ℂ)
  set Z := riemannZeta (2 * n)
  set Z' := deriv riemannZeta (2 * n)
  set Z1 := deriv riemannZeta (1 - 2 * n)
  set P := (2 * (π : ℂ)) ^ (2 * n)
  set e := (-1 : ℂ) ^ n
  set L : ℂ := (Real.log (2 * π) : ℂ)
  set ψ := digamma (2 * n)
  set B : ℂ := (bernoulli (2 * n) : ℂ)
  have h' : -Z1 * P = 2 * e * G * (-L * Z + Z' + ψ * Z) := by
    rw [div_mul_eq_mul_div, eq_div_iff hPne] at h; linear_combination h
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hz'' : Z * (4 * n * G) = -e * P * B := by
    rw [hz, hF, hP, pow_succ]
    field_simp
    ring
  have key : 2 * (2 * n * G) * Z' = -e * P * (2 * n * Z1 - (ψ - L) * B) := by
    linear_combination (-2 * n * e) * h' + (-e ^ 2 * (ψ - L)) * hz'' +
      (-(4 * n * G * Z' - e * P * (ψ - L) * B)) * he
  rw [hF, pow_succ]
  field_simp
  linear_combination key

/-! ### §25.6(iii) Recursion formulas -/

/-- Sum over `range (2n+1)` of a function vanishing at odd arguments. -/
lemma q25a_sum_range_even {M : Type*} [AddCommMonoid M] (g : ℕ → M)
    (hg : ∀ j, Odd j → g j = 0) (n : ℕ) :
    ∑ j ∈ range (2 * n + 1), g j = ∑ k ∈ range (n + 1), g (2 * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      hg (2 * n + 1) ⟨n, rfl⟩, add_zero, sum_range_succ (n := n + 1)]
    ring_nf

/-- Euler's convolution identity `∑_{k=1}^{n-1} C(2n,2k) B_{2k} B_{2n-2k} = -(2n+1) B_{2n}`,
`n ≥ 2` (from DLMF 24.14.2). -/
lemma q25a_bernoulli_convolution {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ Finset.Ico 1 n, ((2 * n).choose (2 * k) : ℚ) * bernoulli (2 * k) *
      bernoulli (2 * n - 2 * k) = -(2 * n + 1) * bernoulli (2 * n) := by
  have h := DLMF.BernoulliEuler.sum_choose_bernoulli_mul_bernoulli_number (2 * n)
  have hodd : bernoulli (2 * n - 1) = 0 :=
    bernoulli_eq_zero_of_odd ⟨n - 1, by omega⟩ (by omega)
  rw [hodd, mul_zero, sub_zero, q25a_sum_range_even _ ?_ n] at h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [sum_range_succ, sum_range_succ'] at h
    rw [Finset.sum_Ico_eq_sum_range, show m + 2 - 1 = m + 1 by omega]
    simp only [Nat.sub_self, mul_zero, Nat.sub_zero, Nat.choose_self, Nat.choose_zero_right,
      bernoulli_zero, Nat.cast_one, mul_one, one_mul] at h
    have e : ∑ k ∈ range (m + 1), ((2 * (m + 2)).choose (2 * (1 + k)) : ℚ) *
        bernoulli (2 * (1 + k)) * bernoulli (2 * (m + 2) - 2 * (1 + k)) =
        ∑ i ∈ range (m + 1), ((2 * (m + 2)).choose (2 * (i + 1)) : ℚ) *
          bernoulli (2 * (i + 1)) * bernoulli (2 * (m + 2) - 2 * (i + 1)) := by
      refine sum_congr rfl fun i _ => ?_; rw [add_comm 1 i]
    rw [e]
    push_cast at h ⊢
    linear_combination h
  · intro j hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have : j = 1 := by obtain ⟨m, rfl⟩ := hj; omega
      subst this
      rw [bernoulli_eq_zero_of_odd (n := 2 * n - 1) ⟨n - 1, by omega⟩ (by omega)]
      ring
    · rw [bernoulli_eq_zero_of_odd hj (by omega)]; ring

/-- `ζ(2k) ζ(2n-2k) = (-1)ⁿ 2^{2n-2} π^{2n}/(2n)! · C(2n,2k) B_{2k} B_{2n-2k}` for `1 ≤ k < n`. -/
lemma q25a_zeta_mul_zeta {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    riemannZeta (2 * k) * riemannZeta (2 * n - 2 * k) =
      (-1) ^ n * 2 ^ (2 * n - 2) * (π : ℂ) ^ (2 * n) / (2 * n)! *
        (((2 * n).choose (2 * k) : ℚ) * bernoulli (2 * k) * bernoulli (2 * n - 2 * k) : ℚ) := by
  have e : (2 * n - 2 * k : ℂ) = 2 * ((n - k : ℕ) : ℂ) := by
    rw [Nat.cast_sub hkn.le]; ring
  rw [e, riemannZeta_two_mul_nat (by omega), riemannZeta_two_mul_nat (by omega)]
  have hc := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ 2 * n by omega)
  rw [show 2 * n - 2 * k = 2 * (n - k) by omega] at hc ⊢
  have hc' : ((2 * n).choose (2 * k) : ℂ) * (2 * k)! * (2 * (n - k))! = (2 * n)! := by
    exact_mod_cast hc
  have h1 : ((2 * k)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2 : ((2 * (n - k))! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : ((2 * n)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have p1 : (-1 : ℂ) ^ (k + 1) * (-1) ^ (n - k + 1) = (-1) ^ n := by
    rw [← pow_add, show k + 1 + (n - k + 1) = n + 2 by omega, pow_add]; norm_num
  have p2 : (2 : ℂ) ^ (2 * k - 1) * 2 ^ (2 * (n - k) - 1) = 2 ^ (2 * n - 2) := by
    rw [← pow_add]; congr 1; omega
  have p3 : (π : ℂ) ^ (2 * k) * (π : ℂ) ^ (2 * (n - k)) = (π : ℂ) ^ (2 * n) := by
    rw [← pow_add]; congr 1; omega
  have hch : ((2 * n).choose (2 * k) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 * k ≤ 2 * n)).ne'
  push_cast
  rw [show ∀ a b c d f g h i j l : ℂ, a * b * c * d / f * (g * h * i * j / l) =
      (a * g) * (b * h) * (c * i) * (d * j) / (f * l) by intros; ring, p1, p2, p3, ← hc']
  field_simp


/-- DLMF 25.6.16: `(n + ½) ζ(2n) = ∑_{k=1}^{n-1} ζ(2k) ζ(2n-2k)` for `n ≥ 2`. -/
@[dlmf 25.6.E16]
theorem riemannZeta_two_mul_recursion {n : ℕ} (hn : 2 ≤ n) :
    (n + 1 / 2 : ℂ) * riemannZeta (2 * n) =
      ∑ k ∈ Finset.Ico 1 n, riemannZeta (2 * k) * riemannZeta (2 * n - 2 * k) := by
  rw [sum_congr rfl fun k hk => q25a_zeta_mul_zeta (mem_Ico.mp hk).1 (mem_Ico.mp hk).2,
    ← mul_sum]
  have h := q25a_bernoulli_convolution hn
  have h' : (∑ k ∈ Finset.Ico 1 n, ((((2 * n).choose (2 * k) : ℚ) * bernoulli (2 * k) *
      bernoulli (2 * n - 2 * k) : ℚ) : ℂ)) = -(2 * n + 1) * (bernoulli (2 * n) : ℂ) := by
    rw [← Rat.cast_sum, h]; push_cast; ring
  rw [h', riemannZeta_two_mul_nat (by omega)]
  have p2 : (2 : ℂ) ^ (2 * n - 1) = 2 * 2 ^ (2 * n - 2) := by
    rw [← pow_succ']; congr 1; omega
  rw [p2, pow_succ]
  have h3 : ((2 * n)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

/-- DLMF 25.6.19, proved from 25.6.16 by the reflection `k ↦ m+n+1-k`. -/
lemma q25a_recursion_two {m n : ℕ} (hmn : 1 ≤ m + n) :
    (m + n + 3 / 2 : ℂ) * riemannZeta (2 * m + 2 * n + 2) =
      ∑ k ∈ Finset.Icc 1 m, riemannZeta (2 * k) * riemannZeta (2 * m + 2 * n + 2 - 2 * k) +
        ∑ k ∈ Finset.Icc 1 n, riemannZeta (2 * k) * riemannZeta (2 * m + 2 * n + 2 - 2 * k) := by
  set g : ℕ → ℂ := fun k => riemannZeta (2 * k) * riemannZeta (2 * m + 2 * n + 2 - 2 * k)
    with hg
  have h := riemannZeta_two_mul_recursion (n := m + n + 1) (by omega)
  have e1 : ((m + n + 1 : ℕ) + 1 / 2 : ℂ) = m + n + 3 / 2 := by push_cast; ring
  have e2 : (2 * ((m + n + 1 : ℕ) : ℂ)) = 2 * m + 2 * n + 2 := by push_cast; ring
  rw [e1, e2] at h
  rw [h]
  have hsum : ∀ k : ℕ, riemannZeta (2 * k) * riemannZeta (2 * m + 2 * n + 2 - 2 * k) = g k :=
    fun k => rfl
  simp only [hsum]
  have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := rfl
  rw [hIcc, ← Finset.sum_Ico_consecutive _ (show 1 ≤ m + 1 by omega)
    (show m + 1 ≤ m + n + 1 by omega)]
  congr 1
  refine Finset.sum_nbij' (fun k => m + n + 1 - k) (fun k => m + n + 1 - k) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Ico, Finset.mem_Icc] at *; omega
  · intro k hk; simp only [Finset.mem_Ico, Finset.mem_Icc] at *; omega
  · intro k hk; simp only [Finset.mem_Ico] at *; omega
  · intro k hk; simp only [Finset.mem_Icc] at *; omega
  · intro k hk
    simp only [Finset.mem_Ico] at hk
    simp only [hg]
    rw [Nat.cast_sub (by omega), mul_comm]
    push_cast
    congr 2 <;> ring

/-- DLMF 25.6.17: `(n + ¾) ζ(4n+2) = ∑_{k=1}^{n} ζ(2k) ζ(4n+2-2k)` for `n ≥ 1`. -/
@[dlmf 25.6.E17]
theorem riemannZeta_four_mul_add_two_recursion {n : ℕ} (hn : 1 ≤ n) :
    (n + 3 / 4 : ℂ) * riemannZeta (4 * n + 2) =
      ∑ k ∈ Finset.Icc 1 n, riemannZeta (2 * k) * riemannZeta (4 * n + 2 - 2 * k) := by
  have h := q25a_recursion_two (m := n) (n := n) (by omega)
  rw [show (2 * n + 2 * n + 2 : ℂ) = 4 * n + 2 by ring] at h
  linear_combination h / 2

/-- DLMF 25.6.18: `(n + ¼) ζ(4n) + ½ ζ(2n)² = ∑_{k=1}^{n} ζ(2k) ζ(4n-2k)` for `n ≥ 1`. -/
@[dlmf 25.6.E18]
theorem riemannZeta_four_mul_recursion {n : ℕ} (hn : 1 ≤ n) :
    (n + 1 / 4 : ℂ) * riemannZeta (4 * n) + 1 / 2 * riemannZeta (2 * n) ^ 2 =
      ∑ k ∈ Finset.Icc 1 n, riemannZeta (2 * k) * riemannZeta (4 * n - 2 * k) := by
  have h := q25a_recursion_two (m := n - 1) (n := n) (by omega)
  have e : (2 * ((n - 1 : ℕ) : ℂ) + 2 * n + 2) = 4 * n := by
    rw [Nat.cast_sub hn]; push_cast; ring
  have e' : ((n - 1 : ℕ) : ℂ) + n + 3 / 2 = 2 * n + 1 / 2 := by
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [e, e'] at h
  have hs : ∑ k ∈ Finset.Icc 1 n, riemannZeta (2 * k) * riemannZeta (4 * n - 2 * k) =
      ∑ k ∈ Finset.Icc 1 (n - 1), riemannZeta (2 * k) * riemannZeta (4 * n - 2 * k) +
        riemannZeta (2 * n) ^ 2 := by
    rw [show Finset.Icc 1 n = Finset.Icc 1 (n - 1 + 1) by congr 1; omega,
      sum_Icc_succ_top (by omega), Nat.sub_add_cancel hn,
      show (4 * (n : ℂ) - 2 * n) = 2 * n by ring, sq]
  rw [hs]
  rw [hs] at h
  linear_combination h / 2

/-- DLMF 25.6.19: for `m, n ≥ 0` with `m + n ≥ 1`,
`(m + n + 3/2) ζ(2m+2n+2) = (∑_{k=1}^{m} + ∑_{k=1}^{n}) ζ(2k) ζ(2m+2n+2-2k)`. -/
@[dlmf 25.6.E19]
theorem riemannZeta_two_mul_recursion_two {m n : ℕ} (hmn : 1 ≤ m + n) :
    (m + n + 3 / 2 : ℂ) * riemannZeta (2 * m + 2 * n + 2) =
      ∑ k ∈ Finset.Icc 1 m, riemannZeta (2 * k) * riemannZeta (2 * m + 2 * n + 2 - 2 * k) +
        ∑ k ∈ Finset.Icc 1 n, riemannZeta (2 * k) * riemannZeta (2 * m + 2 * n + 2 - 2 * k) := by
  exact q25a_recursion_two hmn

/-- `aeval x (bernoulli k)` over `ℝ` is `bernoulliFun k x`. -/
lemma r25a_aeval_bernoulli (k : ℕ) (x : ℝ) :
    Polynomial.aeval x (Polynomial.bernoulli k) = bernoulliFun k x := by
  simp [bernoulliFun, Polynomial.aeval_def, Polynomial.eval_map]

/-- DLMF 24.14.1 at `x = ½`, `y = 0`, `m = 2n`, restricted to the even middle terms. -/
lemma r25a_half_conv {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ Finset.Ico 1 n, ((2 : ℝ) / 2 ^ (2 * k) - 1) * ((2 * n).choose (2 * k) : ℝ) *
      (bernoulli (2 * k) : ℝ) * (bernoulli (2 * n - 2 * k) : ℝ) =
      -(2 * n : ℝ) * (2 / 2 ^ (2 * n) - 1) * bernoulli (2 * n) - bernoulli (2 * n) := by
  have h := DLMF.BernoulliEuler.sum_choose_bernoulli_mul_bernoulli (A := ℝ) (2 * n) 2⁻¹ 0
  simp only [r25a_aeval_bernoulli, add_zero, bernoulliFun_eval_half, bernoulliFun_eval_zero,
    nsmul_eq_mul] at h
  have hodd : bernoulli (2 * n - 1) = 0 :=
    bernoulli_eq_zero_of_odd ⟨n - 1, by omega⟩ (by omega)
  simp only [hodd, Rat.cast_zero, mul_zero, zero_sub] at h
  rw [q25a_sum_range_even _ ?_ n] at h
  · rw [sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)] at h
    simp only [mul_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.sub_self, Nat.choose_self,
      bernoulli_zero, pow_zero, Nat.cast_one, Rat.cast_one] at h
    have e : ∑ k ∈ Finset.Ico 1 n, ((2 * n).choose (2 * k) : ℝ) *
        ((2 / 2 ^ (2 * k) - 1) * (bernoulli (2 * k) : ℝ)) * (bernoulli (2 * n - 2 * k) : ℝ) =
        ∑ k ∈ Finset.Ico 1 n, ((2 : ℝ) / 2 ^ (2 * k) - 1) * ((2 * n).choose (2 * k) : ℝ) *
          (bernoulli (2 * k) : ℝ) * (bernoulli (2 * n - 2 * k) : ℝ) :=
      sum_congr rfl fun k _ => by ring
    rw [← e]
    push_cast at h
    linear_combination h
  · intro j hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have : j = 1 := by obtain ⟨m, rfl⟩ := hj; omega
      subst this; norm_num
    · rw [bernoulli_eq_zero_of_odd hj (by omega)]; simp

/-- `∑_{k=1}^{n-1} (2^{2n-2k}-1) C(2n,2k) B_{2k} B_{2n-2k} = -(2^{2n}-1) B_{2n}`, `n ≥ 2`. -/
lemma r25a_pow_conv {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ Finset.Ico 1 n, ((2 : ℝ) ^ (2 * n - 2 * k) - 1) *
      ((((2 * n).choose (2 * k) : ℚ) * bernoulli (2 * k) * bernoulli (2 * n - 2 * k) : ℚ) : ℝ) =
      -((2 : ℝ) ^ (2 * n) - 1) * bernoulli (2 * n) := by
  have h1 := r25a_half_conv hn
  have h0 : ∑ k ∈ Finset.Ico 1 n, ((((2 * n).choose (2 * k) : ℚ) * bernoulli (2 * k) *
      bernoulli (2 * n - 2 * k) : ℚ) : ℝ) = -(2 * n + 1) * (bernoulli (2 * n) : ℝ) := by
    rw [← Rat.cast_sum, q25a_bernoulli_convolution hn]; push_cast; ring
  have hP : (2 : ℝ) ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have e : ∀ k ∈ Finset.Ico 1 n, ((2 : ℝ) ^ (2 * n - 2 * k) - 1) *
      ((((2 * n).choose (2 * k) : ℚ) * bernoulli (2 * k) * bernoulli (2 * n - 2 * k) : ℚ) : ℝ) =
      2 ^ (2 * n - 1) * (((2 : ℝ) / 2 ^ (2 * k) - 1) * ((2 * n).choose (2 * k) : ℝ) *
        (bernoulli (2 * k) : ℝ) * (bernoulli (2 * n - 2 * k) : ℝ)) +
      (2 ^ (2 * n - 1) - 1) * ((((2 * n).choose (2 * k) : ℚ) * bernoulli (2 * k) *
        bernoulli (2 * n - 2 * k) : ℚ) : ℝ) := by
    intro k hk
    have hk' := (Finset.mem_Ico.mp hk)
    have hq : (2 : ℝ) ^ (2 * n - 2 * k) * 2 ^ (2 * k) = 2 ^ (2 * n) := by
      rw [← pow_add]; congr 1; omega
    have hne : (2 : ℝ) ^ (2 * k) ≠ 0 := pow_ne_zero _ two_ne_zero
    have h2 : (2 : ℝ) ^ (2 * n - 1) * (2 / 2 ^ (2 * k)) = 2 ^ (2 * n - 2 * k) := by
      rw [mul_div_assoc', ← pow_succ, show 2 * n - 1 + 1 = 2 * n - 2 * k + 2 * k by omega,
        pow_add, mul_div_cancel_right₀ _ hne]
    push_cast
    rw [← h2]
    ring
  rw [sum_congr rfl e, sum_add_distrib, ← mul_sum, ← mul_sum, h1, h0, hP]
  field_simp
  ring

/-- DLMF 25.6.20: `½ (2^{2n} - 1) ζ(2n) = ∑_{k=1}^{n-1} (2^{2n-2k} - 1) ζ(2n-2k) ζ(2k)` for
`n ≥ 2`. -/
@[dlmf 25.6.E20]
theorem riemannZeta_two_mul_recursion_pow_two {n : ℕ} (hn : 2 ≤ n) :
    1 / 2 * (2 ^ (2 * n) - 1 : ℂ) * riemannZeta (2 * n) =
      ∑ k ∈ Finset.Ico 1 n, (2 ^ (2 * n - 2 * k) - 1 : ℂ) * riemannZeta (2 * n - 2 * k) *
        riemannZeta (2 * k) := by
  have e : ∀ k ∈ Finset.Ico 1 n, (2 ^ (2 * n - 2 * k) - 1 : ℂ) * riemannZeta (2 * n - 2 * k) *
      riemannZeta (2 * k) = (-1) ^ n * 2 ^ (2 * n - 2) * (π : ℂ) ^ (2 * n) / (2 * n)! *
        ((((2 : ℝ) ^ (2 * n - 2 * k) - 1) *
        ((((2 * n).choose (2 * k) : ℚ) * bernoulli (2 * k) * bernoulli (2 * n - 2 * k) : ℚ) : ℝ)
          : ℝ) : ℂ) := by
    intro k hk
    rw [mul_assoc, mul_comm (riemannZeta _), q25a_zeta_mul_zeta (mem_Ico.mp hk).1
      (mem_Ico.mp hk).2]
    push_cast; ring
  rw [sum_congr rfl e, ← mul_sum, ← ofReal_sum, r25a_pow_conv hn,
    riemannZeta_two_mul_nat (by omega)]
  have p2 : (2 : ℂ) ^ (2 * n - 1) = 2 * 2 ^ (2 * n - 2) := by
    rw [← pow_succ']; congr 1; omega
  rw [p2, pow_succ]
  have h3 : ((2 * n)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  push_cast
  field_simp

end DLMF.Zeta
