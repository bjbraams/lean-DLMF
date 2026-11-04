/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Summability.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Pochhammer.Gamma
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Fractional integrals and derivatives (DLMF §1.15(vi)–(vii))

Properties of the Riemann–Liouville fractional integral `fractionalIntegral` (1.15.47) and the
fractional derivative `fractionalDerivative` (1.15.51, with `n = ⌊ℜα⌋ + 1`), defined in
`Summability/Basic.lean`.

## Main results

* `fractionalIntegral_eq_riemannLiouvilleIntegralFrom`: agreement with the variant of §1.15(vi)
  with lower limit `0`.
* `fractionalIntegral_fractionalIntegral`: the semigroup law `I^α I^β = I^{α+β}` (DLMF 1.15.48),
  by Fubini on the triangle `0 < u < t < x` and the Beta integral.
* `continuousOn_fractionalIntegral`: `I^α f` is continuous on `[0, ∞)`.
* `fractionalIntegral_cpow`: the power rule `I^α t^μ = Γ(μ+1)/Γ(μ+α+1) x^{μ+α}`, the termwise
  form of 1.15.50, by Mathlib's Beta integral `Complex.Gamma_mul_Gamma_eq_betaIntegral`.
* `hasSum_fractionalIntegral_of_hasSum`: the power-series formula (DLMF 1.15.49–1.15.50).
* `fractionalDerivative_eq_iteratedDeriv`: independence of `n` (DLMF 1.15.51).
* `iteratedDeriv_fractionalIntegral`: DLMF 1.15.52.
* `fractionalDerivative_fractionalDerivative_cpow`: DLMF 1.15.53 for power functions.
* `fractionalDerivative_half_deriv_ne`: `D^{1/2} D ≠ D^{3/2}`.

## Implementation notes

The statements are for `x ≥ 0` (DLMF erratum of version 1.0.1); we take `x > 0` where
derivatives in `x` occur and `f` continuous on `[0, ∞)`.

**Missing hypothesis (1.15.53).** DLMF states `D^α D^β = D^{α+β}` whenever none of `α`, `β`,
`α + β` is an integer, without a condition on `f`. This fails in general: for `f(x) = x^{β-1}`
(`ℜβ > 0`), `I^{n-β} f = (Γ(β)/Γ(n)) x^{n-1}` by the power rule, so `D^β f = 0` and
`D^α D^β f = 0`, while `D^{α+β} f = (Γ(β)/Γ(-α)) x^{-α-1} ≠ 0`; e.g. `α = 1/2`, `β = 1/3`. We
state 1.15.53 for power functions `x^μ` with `ℜμ > -1` and `ℜ(μ - β) > -1`
(`fractionalDerivative_fractionalDerivative_cpow`), where it holds by the power rule.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped Nat

namespace DLMF.AlgebraicAnalytic

/-- DLMF §1.15(vi): `fractionalIntegral` (1.15.47) is the variant with lower limit `a = 0`. -/
@[dlmf 1.15.vi]
theorem fractionalIntegral_eq_riemannLiouvilleIntegralFrom (α : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    fractionalIntegral α f x = riemannLiouvilleIntegralFrom 0 α f x := rfl

/-- DLMF 1.15.50 for a single power (power rule): for `ℜα > 0`, `ℜμ > -1` and `x > 0`,
`I^α t^μ = Γ(μ+1)/Γ(μ+α+1) x^{μ+α}`. For `μ = k` this is the `k`-th term of 1.15.50,
`k!/Γ(k+α+1) x^{k+α}`; stronger than DLMF (complex `μ`). -/
@[dlmf 1.15.E50]
theorem fractionalIntegral_cpow {α μ : ℂ} (hα : 0 < α.re) (hμ : -1 < μ.re) {x : ℝ}
    (hx : 0 < x) :
    fractionalIntegral α (fun t => (t : ℂ) ^ μ) x =
      Complex.Gamma (μ + 1) / Complex.Gamma (μ + α + 1) * (x : ℂ) ^ (μ + α) := by
  unfold fractionalIntegral
  set g : ℝ → ℂ := fun t => ((x - t : ℝ) : ℂ) ^ (α - 1) * (t : ℂ) ^ μ with hg
  have hx0 : (0 : ℝ) ≤ x := hx.le
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have h1 : x • (∫ u in (0 : ℝ)..1, g (x * u)) = ∫ t in (0 : ℝ)..x, g t := by
    have := intervalIntegral.smul_integral_comp_mul_left g x (a := 0) (b := 1)
    simp only [mul_zero, mul_one] at this
    exact this
  have h2 : (∫ u in (0 : ℝ)..1, g (x * u)) =
      (x : ℂ) ^ (α - 1 + μ) * Complex.betaIntegral (μ + 1) α := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le zero_le_one] at hu
    simp only [hg]
    have e1 : ((x - x * u : ℝ) : ℂ) = ((x * (1 - u) : ℝ) : ℂ) := by push_cast; ring
    rw [e1, Complex.ofReal_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hx0 (by linarith [hu.2]),
      Complex.mul_cpow_ofReal_nonneg hx0 hu.1, Complex.cpow_add _ _ hxc]
    push_cast
    ring_nf
  have h3 : (∫ t in (0 : ℝ)..x, g t) = (x : ℂ) ^ (μ + α) * Complex.betaIntegral (μ + 1) α := by
    rw [← h1, h2, Complex.real_smul, ← mul_assoc]
    congr 1
    have hp : (x : ℂ) ^ (μ + α) = x * (x : ℂ) ^ (α - 1 + μ) := by
      rw [show μ + α = 1 + (α - 1 + μ) by ring, Complex.cpow_add _ _ hxc, Complex.cpow_one]
    exact hp.symm
  rw [h3]
  have hb := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := μ + 1) (t := α)
    (by simp; linarith) hα
  have hG : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hα
  have hG2 : Complex.Gamma (μ + 1 + α) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have e : μ + α + 1 = μ + 1 + α := by ring
  rw [e]
  field_simp
  linear_combination (-(x : ℂ) ^ (μ + α)) * hb

/-- The shifted Beta integral `∫_u^x (x-t)^{α-1} (t-u)^{β-1} dt = B(α,β) (x-u)^{α+β-1}`. -/
private lemma integral_cpow_mul_cpow_shift {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) {u x : ℝ}
    (hux : u < x) :
    ∫ t in u..x, ((x - t : ℝ) : ℂ) ^ (α - 1) * ((t - u : ℝ) : ℂ) ^ (β - 1) =
      Complex.Gamma α * Complex.Gamma β / Complex.Gamma (α + β) *
        ((x - u : ℝ) : ℂ) ^ (α + β - 1) := by
  have h := fractionalIntegral_cpow (α := α) (μ := β - 1) hα (by simp; linarith)
    (sub_pos.mpr hux)
  unfold fractionalIntegral at h
  have hs := intervalIntegral.integral_comp_sub_right
    (fun s : ℝ => (((x - u) - s : ℝ) : ℂ) ^ (α - 1) * (s : ℂ) ^ (β - 1)) u (a := u) (b := x)
  simp only [sub_self] at hs
  have he : (fun t : ℝ => ((x - t : ℝ) : ℂ) ^ (α - 1) * ((t - u : ℝ) : ℂ) ^ (β - 1)) =
      fun t => (((x - u) - (t - u) : ℝ) : ℂ) ^ (α - 1) * ((t - u : ℝ) : ℂ) ^ (β - 1) := by
    funext t; congr 3; ring
  rw [he, hs]
  have hg : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hα
  rw [inv_mul_eq_iff_eq_mul₀ hg] at h
  rw [h, show β - 1 + 1 = β by ring, show β - 1 + α + 1 = α + β by ring,
    show β - 1 + α = α + β - 1 by ring]
  field_simp

/-- `∫₀^t (t - u)^{b-1} du = t^b/b` for `b > 0`, `t ≥ 0`. -/
private lemma integral_sub_rpow {b t : ℝ} (hb : 0 < b) :
    ∫ u in (0 : ℝ)..t, (t - u) ^ (b - 1) = t ^ b / b := by
  rw [intervalIntegral.integral_comp_sub_left (fun v => v ^ (b - 1)) t, sub_self, sub_zero,
    integral_rpow (Or.inl (by linarith)), sub_add_cancel, Real.zero_rpow hb.ne', sub_zero]

/-- `u ↦ (t - u)^{b-1}` is integrable on `(0, t]` for `b > 0`. -/
private lemma integrableOn_sub_rpow {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    IntegrableOn (fun u : ℝ => (t - u) ^ (b - 1)) (Ioc 0 t) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (r := b - 1) (a := 0) (b := t)
    (by linarith)).comp_sub_left t
  rw [sub_self, sub_zero] at h
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp h.symm

/-- The kernel `(x - t)^{a-1} (t - u)^{b-1} 1_{u < t}` is integrable on `(0, x)²`. -/
private lemma integrable_betaKernel {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    Integrable (fun p : ℝ × ℝ => if p.2 < p.1 then (x - p.1) ^ (a - 1) * (p.1 - p.2) ^ (b - 1)
      else 0) ((volume.restrict (Ioo 0 x)).prod (volume.restrict (Ioo 0 x))) := by
  set H : ℝ × ℝ → ℝ := fun p => if p.2 < p.1 then (x - p.1) ^ (a - 1) * (p.1 - p.2) ^ (b - 1)
      else 0 with hH
  have hmeas : Measurable H := by
    refine Measurable.ite (measurableSet_lt measurable_snd measurable_fst) ?_ measurable_const
    fun_prop
  have hsec : ∀ t ∈ Ioo 0 x, (fun u => H (t, u)) =
      (Iio t).indicator (fun u => (x - t) ^ (a - 1) * (t - u) ^ (b - 1)) := by
    intro t _
    funext u
    simp only [hH, indicator, mem_Iio]
  have hsecI : ∀ t ∈ Ioo 0 x, Integrable (fun u => H (t, u)) (volume.restrict (Ioo 0 x)) := by
    intro t ht
    rw [hsec t ht, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iio]
    have hI : IntegrableOn (fun u : ℝ => (x - t) ^ (a - 1) * (t - u) ^ (b - 1)) (Ioc 0 t) :=
      (integrableOn_sub_rpow hb ht.1.le).const_mul ((x - t) ^ (a - 1))
    exact hI.mono_set fun u hu => ⟨hu.2.1, hu.1.le⟩
  have hsecV : ∀ t ∈ Ioo 0 x, ∫ u, ‖H (t, u)‖ ∂(volume.restrict (Ioo 0 x)) =
      (x - t) ^ (a - 1) * (t ^ b / b) := by
    intro t ht
    have hnn : ∀ u, 0 ≤ H (t, u) := by
      intro u
      simp only [hH]
      split_ifs with h
      · exact mul_nonneg (Real.rpow_nonneg (by linarith [ht.2]) _)
          (Real.rpow_nonneg (by have : u < t := h; linarith) _)
      · exact le_rfl
    simp_rw [Real.norm_of_nonneg (hnn _)]
    rw [hsec t ht, integral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio, integral_const_mul,
      ← integral_sub_rpow hb, intervalIntegral.integral_of_le ht.1.le]
    congr 1
    refine setIntegral_congr_set ?_
    rw [show Iio t ∩ Ioo 0 x = Ioo 0 t by
      ext u; simp only [mem_inter_iff, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans ht.2⟩]
    exact Ioo_ae_eq_Ioc
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using hsecI t ht
  · have hg : IntegrableOn (fun t : ℝ => (x - t) ^ (a - 1) * (x ^ b / b)) (Ioo 0 x) := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (r := a - 1) (a := 0) (b := x)
        (by linarith)).comp_sub_left x
      rw [sub_self, sub_zero] at h
      have h2 : IntegrableOn (fun t : ℝ => (x - t) ^ (a - 1) * (x ^ b / b)) (Ioc 0 x) :=
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mp h.symm).mul_const _
      exact h2.mono_set Ioo_subset_Ioc_self
    refine hg.mono' hmeas.aestronglyMeasurable.norm.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [hsecV t ht, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith [ht.2]) _)
      (div_nonneg (Real.rpow_nonneg ht.1.le _) hb.le))]
    gcongr
    · exact Real.rpow_nonneg (by linarith [ht.2]) _
    · exact ht.1.le
    · exact ht.2.le

/-- DLMF 1.15.48: `I^α I^β = I^{α+β}` for `ℜα > 0`, `ℜβ > 0`, applied to a function continuous on
`[0, ∞)` at `x ≥ 0`. -/
@[dlmf 1.15.E48]
theorem fractionalIntegral_fractionalIntegral {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Ici 0)) {x : ℝ} (hx : 0 ≤ x) :
    fractionalIntegral α (fractionalIntegral β f) x = fractionalIntegral (α + β) f x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [fractionalIntegral]
  set μ : Measure ℝ := volume.restrict (Ioo 0 x) with hμ
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.mono (Icc_subset_Ici_self : Icc (0 : ℝ) x ⊆ Ici 0))
  set K : ℝ × ℝ → ℂ := fun p => if p.2 < p.1 then
    ((x - p.1 : ℝ) : ℂ) ^ (α - 1) * ((p.1 - p.2 : ℝ) : ℂ) ^ (β - 1) else 0 with hK
  set G : ℝ × ℝ → ℂ := fun p => K p * f p.2 with hG
  have hKm : Measurable K := by
    refine Measurable.ite (measurableSet_lt measurable_snd measurable_fst) ?_ measurable_const
    fun_prop
  have hfm : AEStronglyMeasurable f μ :=
    (hf.mono (Ioo_subset_Ioi_self.trans Ioi_subset_Ici_self)).aestronglyMeasurable
      measurableSet_Ioo
  have hGi : Integrable G (μ.prod μ) := by
    refine ((integrable_betaKernel hα hβ hx).const_mul M).mono'
      (hKm.aestronglyMeasurable.mul hfm.comp_snd) ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    obtain ⟨⟨ht0, htx⟩, ⟨hu0, hux⟩⟩ := hp
    have hfu : ‖f p.2‖ ≤ M := hM p.2 ⟨hu0.le, hux.le⟩
    simp only [hG, hK]
    split_ifs with h
    · rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos (by linarith),
        norm_cpow_eq_rpow_re_of_pos (by linarith), sub_re, one_re, sub_re, one_re]
      have h1 : 0 ≤ (x - p.1) ^ (α.re - 1) := Real.rpow_nonneg (by linarith) _
      have h2 : 0 ≤ (p.1 - p.2) ^ (β.re - 1) := Real.rpow_nonneg (by linarith) _
      calc (x - p.1) ^ (α.re - 1) * (p.1 - p.2) ^ (β.re - 1) * ‖f p.2‖ ≤
            (x - p.1) ^ (α.re - 1) * (p.1 - p.2) ^ (β.re - 1) * M := by gcongr
        _ = _ := by ring
    · simp
  have hA : ∀ t ∈ Ioo 0 x, ∫ u, G (t, u) ∂μ =
      ((x - t : ℝ) : ℂ) ^ (α - 1) * ∫ u in (0 : ℝ)..t, ((t - u : ℝ) : ℂ) ^ (β - 1) * f u := by
    intro t ht
    have he : (fun u => G (t, u)) = (Iio t).indicator
        (fun u => ((x - t : ℝ) : ℂ) ^ (α - 1) * (((t - u : ℝ) : ℂ) ^ (β - 1) * f u)) := by
      funext u
      simp only [hG, hK, indicator, mem_Iio]
      split_ifs <;> ring
    rw [he, integral_indicator measurableSet_Iio, hμ,
      Measure.restrict_restrict measurableSet_Iio,
      show Iio t ∩ Ioo 0 x = Ioo 0 t by
        ext u; simp only [mem_inter_iff, mem_Iio, mem_Ioo]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans ht.2⟩,
      integral_const_mul, intervalIntegral.integral_of_le ht.1.le, integral_Ioc_eq_integral_Ioo]
  have hB : ∀ u ∈ Ioo 0 x, ∫ t, G (t, u) ∂μ =
      Complex.Gamma α * Complex.Gamma β / Complex.Gamma (α + β) *
        (((x - u : ℝ) : ℂ) ^ (α + β - 1) * f u) := by
    intro u hu
    have he : (fun t => G (t, u)) = (Ioi u).indicator
        (fun t => ((x - t : ℝ) : ℂ) ^ (α - 1) * ((t - u : ℝ) : ℂ) ^ (β - 1) * f u) := by
      funext t
      simp only [hG, hK, indicator, mem_Ioi]
      split_ifs <;> ring
    rw [he, integral_indicator measurableSet_Ioi, hμ,
      Measure.restrict_restrict measurableSet_Ioi, integral_mul_const,
      show Ioi u ∩ Ioo 0 x = Ioo u x by
        ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
        constructor
        · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, hu.1.trans h1, h2⟩,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu.2.le,
      integral_cpow_mul_cpow_shift hα hβ hu.2]
    ring
  have hΓα : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hα
  have hΓβ : Complex.Gamma β ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hβ
  have hΓ : Complex.Gamma (α + β) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hL : ∫ t in (0 : ℝ)..x, ((x - t : ℝ) : ℂ) ^ (α - 1) * fractionalIntegral β f t =
      (Complex.Gamma β)⁻¹ * ∫ t, ∫ u, G (t, u) ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo, hμ,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [← hμ, hA t ht, fractionalIntegral]
    ring
  have hswap := integral_integral_swap (μ := μ) (ν := μ) (f := fun t u => G (t, u)) hGi
  have hR : ∫ u, ∫ t, G (t, u) ∂μ ∂μ = Complex.Gamma α * Complex.Gamma β /
      Complex.Gamma (α + β) * ∫ u in (0 : ℝ)..x, ((x - u : ℝ) : ℂ) ^ (α + β - 1) * f u := by
    rw [intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo, ← integral_const_mul,
      hμ]
    exact setIntegral_congr_fun measurableSet_Ioo fun u hu => by rw [← hμ, hB u hu]
  conv_lhs => rw [fractionalIntegral]
  rw [hL, hswap, hR]
  conv_rhs => rw [fractionalIntegral]
  field_simp

/-- DLMF 1.15.49–1.15.50: if `f(t) = ∑ a_k t^k` on `[0, x]` with `∑ |a_k| x^k < ∞`, then
`I^α f(x) = ∑ k!/Γ(k+α+1) a_k x^{k+α}` for `ℜα > 0`, `x > 0`. -/
@[dlmf 1.15.E49, dlmf 1.15.E50]
theorem hasSum_fractionalIntegral_of_hasSum {α : ℂ} (hα : 0 < α.re) {a : ℕ → ℂ}
    {f : ℝ → ℂ} {x : ℝ} (hx : 0 < x) (hs : Summable fun k => ‖a k‖ * x ^ k)
    (hf : ∀ t ∈ Icc 0 x, HasSum (fun k => a k * (t : ℂ) ^ k) (f t)) :
    HasSum (fun k : ℕ => (k ! : ℂ) / Complex.Gamma (k + α + 1) * a k * (x : ℂ) ^ (k + α))
      (fractionalIntegral α f x) := by
  have hker : IntervalIntegrable (fun t : ℝ => ((x - t : ℝ) : ℂ) ^ (α - 1)) volume 0 x := by
    have h := (intervalIntegral.intervalIntegrable_cpow' (a := x - x) (b := x - 0) (r := α - 1)
      (by simp; linarith)).comp_sub_left x
    simpa using h.symm
  set F : ℕ → ℝ → ℂ := fun k t => ((x - t : ℝ) : ℂ) ^ (α - 1) * (a k * (t : ℂ) ^ k) with hF
  have hmeas : ∀ k, AEStronglyMeasurable (F k) (volume.restrict (Set.uIoc 0 x)) := by
    intro k
    have := (hker.mul_continuousOn (g := fun t : ℝ => a k * (t : ℂ) ^ k)
      (by fun_prop)).def'
    simpa [hF] using this.aestronglyMeasurable
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := F) (f := fun t => ((x - t : ℝ) : ℂ) ^ (α - 1) * f t)
    (fun k t => ‖((x - t : ℝ) : ℂ) ^ (α - 1)‖ * (‖a k‖ * x ^ k)) hmeas
    (fun k => Eventually.of_forall fun t ht => by
      rw [uIoc_of_le hx.le] at ht
      simp only [hF, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
      gcongr
      all_goals linarith [ht.1, ht.2])
    (Eventually.of_forall fun t _ => hs.mul_left _)
    (by simp_rw [tsum_mul_left]; exact hker.norm.mul_const _)
    (Eventually.of_forall fun t ht => by
      rw [uIoc_of_le hx.le] at ht
      exact (hf t ⟨ht.1.le, ht.2⟩).mul_left _)
  have hmul := key.mul_left (Complex.Gamma α)⁻¹
  unfold fractionalIntegral
  refine hmul.congr_fun fun k => ?_
  have hc := fractionalIntegral_cpow (μ := (k : ℂ)) hα (by simp; linarith [k.cast_nonneg (α := ℝ)])
    hx
  unfold fractionalIntegral at hc
  simp only [hF]
  simp_rw [Complex.cpow_natCast] at hc
  rw [Complex.Gamma_nat_eq_factorial] at hc
  have he : (∫ t in (0 : ℝ)..x, ((x - t : ℝ) : ℂ) ^ (α - 1) * (a k * (t : ℂ) ^ k)) =
      a k * ∫ t in (0 : ℝ)..x, ((x - t : ℝ) : ℂ) ^ (α - 1) * (t : ℂ) ^ k := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  rw [he]
  linear_combination (-a k) * hc

/-- The fractional integral after the substitution `t = x - s`, written over a fixed interval
`(0, X)` with an indicator. -/
private lemma integral_fractionalKernel_eq {α : ℂ} {f : ℝ → ℂ} {x X : ℝ} (hx : 0 ≤ x)
    (hxX : x < X) :
    ∫ t in (0 : ℝ)..x, ((x - t : ℝ) : ℂ) ^ (α - 1) * f t =
      ∫ s in Ioo 0 X, (Iio x).indicator (fun s : ℝ => (s : ℂ) ^ (α - 1) * f (x - s)) s := by
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    show Iio x ∩ Ioo 0 X = Ioo 0 x by
      ext u; simp only [mem_inter_iff, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hxX⟩,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx]
  have h := intervalIntegral.integral_comp_sub_left
    (fun s : ℝ => (s : ℂ) ^ (α - 1) * f (x - s)) x (a := 0) (b := x)
  simp only [sub_self, sub_zero, sub_sub_cancel] at h
  exact h

/-- DLMF §1.15(vi): the fractional integral of a function continuous on `[0, ∞)` is continuous
on `[0, ∞)` for `ℜα > 0`. -/
theorem continuousOn_fractionalIntegral {α : ℂ} (hα : 0 < α.re) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ici 0)) : ContinuousOn (fractionalIntegral α f) (Ici 0) := by
  intro x₀ hx₀
  have hx₀' : (0 : ℝ) ≤ x₀ := hx₀
  set X := x₀ + 1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.mono (Icc_subset_Ici_self : Icc (0 : ℝ) X ⊆ Ici 0))
  set F : ℝ → ℝ → ℂ := fun x => (Iio x).indicator (fun s : ℝ => (s : ℂ) ^ (α - 1) * f (x - s))
  have hev : ∀ᶠ x in 𝓝[Ici 0] x₀, 0 ≤ x ∧ x < X :=
    eventually_mem_nhdsWithin.and
      (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by linarith)))
  have heq : ∀ᶠ x in 𝓝[Ici 0] x₀, fractionalIntegral α f x =
      (Complex.Gamma α)⁻¹ * ∫ s in Ioo 0 X, F x s := by
    filter_upwards [hev] with x hx
    rw [fractionalIntegral, integral_fractionalKernel_eq hx.1 hx.2]
  have hcont : ContinuousWithinAt (fun x => ∫ s in Ioo 0 X, F x s) (Ici 0) x₀ := by
    refine continuousWithinAt_of_dominated (bound := fun s => M * s ^ (α.re - 1)) ?_ ?_ ?_ ?_
    · filter_upwards [hev] with x hx
      refine (aestronglyMeasurable_indicator_iff measurableSet_Iio).mpr ?_
      rw [Measure.restrict_restrict measurableSet_Iio]
      refine ContinuousOn.aestronglyMeasurable (fun s hs => ?_) (measurableSet_Iio.inter
        measurableSet_Ioo)
      have hs0 : 0 < s := hs.2.1
      have hsx : s < x := hs.1
      refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
      · exact ContinuousAt.cpow (f := fun u : ℝ => (u : ℂ)) continuous_ofReal.continuousAt
          continuousAt_const (by simpa using hs0)
      · refine ContinuousAt.comp (g := f) ?_ (by fun_prop)
        exact hf.continuousAt (Ici_mem_nhds (by linarith))
    · filter_upwards [hev] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      simp only [F, indicator]
      split_ifs with h
      · have hsx : s < x := h
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hs.1, sub_re, one_re]
        calc s ^ (α.re - 1) * ‖f (x - s)‖ ≤ s ^ (α.re - 1) * M :=
              mul_le_mul_of_nonneg_left (hM _ ⟨by linarith, by linarith [hs.1]⟩)
                (Real.rpow_nonneg hs.1.le _)
          _ = M * s ^ (α.re - 1) := mul_comm _ _
      · simp only [norm_zero]
        exact mul_nonneg ((norm_nonneg _).trans (hM 0 ⟨le_rfl, by linarith⟩))
          (Real.rpow_nonneg hs.1.le _)
    · have h := intervalIntegral.intervalIntegrable_rpow' (r := α.re - 1) (a := 0) (b := X)
        (by linarith)
      have h2 : IntegrableOn (fun s : ℝ => M * s ^ (α.re - 1)) (Ioc 0 X) :=
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp h).const_mul M
      exact h2.mono_set Ioo_subset_Ioc_self
    · have hne : ∀ᵐ s ∂(volume.restrict (Ioo 0 X)), s ≠ x₀ := by
        refine ae_restrict_of_ae ?_
        simp [ae_iff]
      filter_upwards [hne] with s hs
      rcases hs.lt_or_gt with h | h
      · -- `s < x₀`: eventually `s < x`
        refine ContinuousAt.continuousWithinAt ?_
        have he : (fun x => F x s) =ᶠ[𝓝 x₀] fun x => (s : ℂ) ^ (α - 1) * f (x - s) := by
          filter_upwards [Ioi_mem_nhds h] with x hx
          simp [F, show s < x from hx]
        refine ContinuousAt.congr ?_ he.symm
        refine continuousAt_const.mul (ContinuousAt.comp (g := f) ?_ (by fun_prop))
        exact hf.continuousAt (Ici_mem_nhds (by linarith))
      · refine ContinuousAt.continuousWithinAt ?_
        have he : (fun x => F x s) =ᶠ[𝓝 x₀] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds h] with x hx
          simp [F, show ¬ s < x from not_lt.mpr hx.le]
        exact ContinuousAt.congr continuousAt_const he.symm
  refine ContinuousWithinAt.congr_of_eventuallyEq (hcont.const_mul _) heq ?_
  exact heq.self_of_nhdsWithin hx₀

/-- `I¹ g(x) = ∫₀^x g`. -/
private lemma fractionalIntegral_one (g : ℝ → ℂ) :
    fractionalIntegral 1 g = fun x => ∫ t in (0 : ℝ)..x, g t := by
  funext x
  simp [fractionalIntegral]

/-- `d/dx I¹ g(x) = g(x)` for `x > 0` and `g` continuous on `[0, ∞)`. -/
private lemma hasDerivAt_fractionalIntegral_one {g : ℝ → ℂ} (hg : ContinuousOn g (Ici 0)) {x : ℝ}
    (hx : 0 < x) : HasDerivAt (fractionalIntegral 1 g) (g x) x := by
  rw [fractionalIntegral_one]
  refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
  · exact (hg.mono (by rw [uIcc_of_le hx.le]; exact Icc_subset_Ici_self)).intervalIntegrable
  · exact (hg.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi x hx
  · exact hg.continuousAt (Ici_mem_nhds hx)

/-- `Dʲ Iʲ g = g` on `(0, ∞)` for `j ≥ 1` and `g` continuous on `[0, ∞)`. -/
private lemma iteratedDeriv_fractionalIntegral_natCast {g : ℝ → ℂ} (hg : ContinuousOn g (Ici 0))
    (j : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (j + 1) (fractionalIntegral ((j + 1 : ℕ) : ℂ) g) x = g x := by
  induction j generalizing x with
  | zero =>
    simpa using (hasDerivAt_fractionalIntegral_one hg hx).deriv
  | succ j ih =>
    set h := fractionalIntegral ((j + 1 : ℕ) : ℂ) g
    have hh : ContinuousOn h (Ici 0) :=
      continuousOn_fractionalIntegral (by simp; positivity) hg
    have hsemi : ∀ y, 0 ≤ y → fractionalIntegral ((j + 1 + 1 : ℕ) : ℂ) g y =
        fractionalIntegral 1 h y := by
      intro y hy
      rw [show ((j + 1 + 1 : ℕ) : ℂ) = 1 + ((j + 1 : ℕ) : ℂ) by push_cast; ring]
      exact (fractionalIntegral_fractionalIntegral (α := 1) (β := ((j + 1 : ℕ) : ℂ))
        (by simp) (by simp; positivity) hg hy).symm
    have hderiv : ∀ y, 0 < y →
        deriv (fractionalIntegral ((j + 1 + 1 : ℕ) : ℂ) g) y = h y := by
      intro y hy
      have he : fractionalIntegral ((j + 1 + 1 : ℕ) : ℂ) g =ᶠ[𝓝 y] fractionalIntegral 1 h := by
        filter_upwards [Ioi_mem_nhds hy] with z hz using hsemi z (le_of_lt hz)
      rw [he.deriv_eq]
      exact (hasDerivAt_fractionalIntegral_one hh hy).deriv
    have he : deriv (fractionalIntegral ((j + 1 + 1 : ℕ) : ℂ) g) =ᶠ[𝓝 x] h := by
      filter_upwards [Ioi_mem_nhds hx] with y hy using hderiv y hy
    rw [iteratedDeriv_succ', (he.iteratedDeriv (j + 1)).eq_of_nhds]
    exact ih hx

/-- `Dᵏ⁺ᵈ⁺¹ Iᵈ⁺¹ h = Dᵏ h` at `x > 0` when `I^{d+1} h` is replaced by a function `F` agreeing
with it on `[0, ∞)`. -/
private lemma iteratedDeriv_add_of_eqOn {h F : ℝ → ℂ} (hh : ContinuousOn h (Ici 0)) (k d : ℕ)
    (hF : ∀ y, 0 ≤ y → F y = fractionalIntegral ((d + 1 : ℕ) : ℂ) h y) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (k + (d + 1)) F x = iteratedDeriv k h x := by
  have he : iteratedDeriv (d + 1) F =ᶠ[𝓝 x] h := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hFy : F =ᶠ[𝓝 y] fractionalIntegral ((d + 1 : ℕ) : ℂ) h := by
      filter_upwards [Ioi_mem_nhds hy] with z hz using hF z (le_of_lt hz)
    rw [(hFy.iteratedDeriv (d + 1)).eq_of_nhds]
    exact iteratedDeriv_fractionalIntegral_natCast hh d hy
  rw [iteratedDeriv_eq_iterate, Function.iterate_add_apply, ← iteratedDeriv_eq_iterate,
    ← iteratedDeriv_eq_iterate, (he.iteratedDeriv k).eq_of_nhds]

/-- DLMF 1.15.51 (independence of `n`): for any integer `n > ℜα > 0`, `f` continuous on `[0, ∞)`
and `x > 0`, `(dⁿ/dxⁿ) I^{n-α} f(x)` equals `fractionalDerivative α f x` (defined with
`n = ⌊ℜα⌋ + 1`). -/
@[dlmf 1.15.E51]
theorem fractionalDerivative_eq_iteratedDeriv {α : ℂ} (hα : 0 < α.re) {n : ℕ}
    (hn : α.re < n) {f : ℝ → ℂ} (hf : ContinuousOn f (Ici 0)) {x : ℝ} (hx : 0 < x) :
    fractionalDerivative α f x = iteratedDeriv n (fractionalIntegral ((n : ℂ) - α) f) x := by
  set m := fractionalDerivativeOrder α with hm
  have hmn : m ≤ n := by
    rw [hm, fractionalDerivativeOrder, Nat.add_one_le_iff]
    exact (Nat.floor_lt hα.le).mpr hn
  have hmα : 0 < ((m : ℂ) - α).re := by
    simp only [sub_re, natCast_re, hm, fractionalDerivativeOrder]
    have := Nat.lt_floor_add_one α.re
    push_cast
    linarith
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rcases d with _ | d
  · simp [fractionalDerivative, hm]
  rw [fractionalDerivative, ← hm]
  refine (iteratedDeriv_add_of_eqOn (continuousOn_fractionalIntegral hmα hf) m d
    (fun y hy => ?_) hx).symm
  rw [fractionalIntegral_fractionalIntegral (by simp; positivity) hmα hf hy]
  congr 1
  push_cast; ring

/-- DLMF 1.15.52: `D^k I^α = D^n I^{α+n-k}` for `k = 1, …, n` (`D^k` the ordinary `k`-th
derivative), for `ℜα > 0`, `f` continuous on `[0, ∞)` and `x > 0`. -/
@[dlmf 1.15.E52]
theorem iteratedDeriv_fractionalIntegral {α : ℂ} (hα : 0 < α.re) {k n : ℕ} (hk : k ≤ n)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Ici 0)) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (fractionalIntegral α f) x =
      iteratedDeriv n (fractionalIntegral (α + n - k) f) x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rcases d with _ | d
  · simp
  refine (iteratedDeriv_add_of_eqOn (continuousOn_fractionalIntegral hα hf) k d
    (fun y hy => ?_) hx).symm
  rw [fractionalIntegral_fractionalIntegral (by simp; positivity) hα hf hy]
  congr 1
  push_cast; ring

/-- `dᵏ/dyᵏ y^c = c(c-1)⋯(c-k+1) y^{c-k}` for `y > 0`. -/
private lemma iteratedDeriv_ofReal_cpow (c : ℂ) (k : ℕ) {y : ℝ} (hy : 0 < y) :
    iteratedDeriv k (fun y : ℝ => (y : ℂ) ^ c) y =
      (descPochhammer ℂ k).eval c * (y : ℂ) ^ (c - k) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    have hev : iteratedDeriv k (fun y : ℝ => (y : ℂ) ^ c) =ᶠ[𝓝 y]
        fun y : ℝ => (descPochhammer ℂ k).eval c * (y : ℂ) ^ (c - k) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz using ih hz
    rw [iteratedDeriv_succ, hev.deriv_eq, deriv_const_mul_field, descPochhammer_succ_eval]
    rcases eq_or_ne (c - k) 0 with h | h
    · have : (fun y : ℝ => (y : ℂ) ^ (c - k)) = fun _ => 1 := by
        funext z; rw [h, Complex.cpow_zero]
      rw [this, deriv_const, h]
      simp
    · rw [Complex.deriv_ofReal_cpow_const hy.ne' h]
      push_cast
      ring_nf

/-- The power rule for the fractional derivative: `D^γ t^μ = Γ(μ+1)/Γ(μ-γ+1) x^{μ-γ}` for
`ℜμ > -1` and `x > 0`. -/
private lemma fractionalDerivative_cpow {γ μ : ℂ} (hμ : -1 < μ.re) {x : ℝ} (hx : 0 < x) :
    fractionalDerivative γ (fun t => (t : ℂ) ^ μ) x =
      Complex.Gamma (μ + 1) / Complex.Gamma (μ - γ + 1) * (x : ℂ) ^ (μ - γ) := by
  set n := fractionalDerivativeOrder γ with hn
  have hnγ : 0 < ((n : ℂ) - γ).re := by
    have : γ.re < n := by
      simp only [hn, fractionalDerivativeOrder, Nat.cast_add, Nat.cast_one]
      exact Nat.lt_floor_add_one _
    simpa using this
  have hev : fractionalIntegral ((n : ℂ) - γ) (fun t => (t : ℂ) ^ μ) =ᶠ[𝓝 x]
      fun y : ℝ => Complex.Gamma (μ + 1) / Complex.Gamma (μ + ((n : ℂ) - γ) + 1) *
        (y : ℂ) ^ (μ + ((n : ℂ) - γ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using fractionalIntegral_cpow hnγ hμ hy
  rw [fractionalDerivative, ← hn, hev.iteratedDeriv_eq, iteratedDeriv_const_mul_field,
    iteratedDeriv_ofReal_cpow _ _ hx, descPochhammer_eval_eq_ascPochhammer]
  have he : μ + ((n : ℂ) - γ) - n = μ - γ := by ring
  rw [he, ← mul_assoc]
  congr 1
  have hg := Complex.one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat (μ - γ + 1) n
  have he2 : μ - γ + 1 + n = μ + ((n : ℂ) - γ) + 1 := by ring
  rw [he2] at hg
  rw [div_eq_mul_inv, div_eq_mul_inv, hg]
  ring

/-- If `g = c h` on `(0, ∞)` then `D^α g = c D^α h` at `x > 0`. -/
private lemma fractionalDerivative_congr_const_mul {α c : ℂ} {g h : ℝ → ℂ}
    (hgh : ∀ t, 0 < t → g t = c * h t) {x : ℝ} (hx : 0 < x) :
    fractionalDerivative α g x = c * fractionalDerivative α h x := by
  have hev : fractionalIntegral ((fractionalDerivativeOrder α : ℂ) - α) g =ᶠ[𝓝 x]
      fun y => c * fractionalIntegral ((fractionalDerivativeOrder α : ℂ) - α) h y := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [fractionalIntegral]
    rw [← mul_assoc, mul_comm c, mul_assoc, ← intervalIntegral.integral_const_mul c]
    congr 1
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hy.le] at ht
    rw [hgh t ht.1]
    ring
  rw [fractionalDerivative, hev.iteratedDeriv_eq, iteratedDeriv_const_mul_field]
  rfl

/-- DLMF 1.15.53, for power functions: if `ℜμ > -1` and `ℜ(μ - β) > -1`, then
`D^α D^β x^μ = D^{α+β} x^μ` for `x > 0`. Stronger than DLMF, which assumes that none of `α`, `β`,
`α + β` is an integer and `ℜα, ℜβ > 0`. -/
@[dlmf 1.15.E53]
theorem fractionalDerivative_fractionalDerivative_cpow' {α β μ : ℂ}
    (hμ : -1 < μ.re) (hμβ : -1 < (μ - β).re) {x : ℝ} (hx : 0 < x) :
    fractionalDerivative α (fractionalDerivative β fun t => (t : ℂ) ^ μ) x =
      fractionalDerivative (α + β) (fun t => (t : ℂ) ^ μ) x := by
  rw [fractionalDerivative_congr_const_mul (h := fun t => (t : ℂ) ^ (μ - β))
      (fun t ht => fractionalDerivative_cpow hμ ht) hx,
    fractionalDerivative_cpow hμβ hx, fractionalDerivative_cpow hμ hx]
  have hG : Complex.Gamma (μ - β + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      have := hμβ; simp only [sub_re, add_re, one_re] at this ⊢; linarith)
  have e1 : μ - β - α + 1 = μ - (α + β) + 1 := by ring
  have e2 : μ - β - α = μ - (α + β) := by ring
  rw [e1, e2]
  field_simp

/-- DLMF 1.15.53, for power functions: if none of `α`, `β`, `α + β` is an integer, `ℜα > 0`,
`ℜβ > 0`, `ℜμ > -1` and `ℜ(μ - β) > -1`, then `D^α D^β x^μ = D^{α+β} x^μ` for `x > 0`. DLMF states
1.15.53 without a hypothesis on `f`, which is false in general (see the module docstring). -/
@[dlmf 1.15.E53]
theorem fractionalDerivative_fractionalDerivative_cpow {α β μ : ℂ} (_hα : 0 < α.re)
    (_hβ : 0 < β.re) (_hαi : ∀ m : ℤ, α ≠ m) (_hβi : ∀ m : ℤ, β ≠ m)
    (_hαβi : ∀ m : ℤ, α + β ≠ m) (hμ : -1 < μ.re) (hμβ : -1 < (μ - β).re) {x : ℝ} (hx : 0 < x) :
    fractionalDerivative α (fractionalDerivative β fun t => (t : ℂ) ^ μ) x =
      fractionalDerivative (α + β) (fun t => (t : ℂ) ^ μ) x :=
  fractionalDerivative_fractionalDerivative_cpow' hμ hμβ hx

/-- DLMF §1.15(vii), after 1.15.53: `D^{1/2} D ≠ D^{3/2}`. For `f = 1`, `D^{1/2}(f') = 0` while
`D^{3/2} f(1) = 1/Γ(-1/2) = -1/(2√π) ≠ 0`. -/
@[dlmf 1.15.vii]
theorem fractionalDerivative_half_deriv_ne :
    fractionalDerivative (1 / 2) (deriv fun _ : ℝ => (1 : ℂ)) 1 ≠
      fractionalDerivative (3 / 2) (fun _ : ℝ => (1 : ℂ)) 1 := by
  have hzero : fractionalDerivative (1 / 2) (deriv fun _ : ℝ => (1 : ℂ)) 1 = 0 := by
    have hz (α : ℂ) : fractionalIntegral α (fun _ : ℝ => (0 : ℂ)) = fun _ => 0 := by
      funext x
      simp [fractionalIntegral]
    simp only [deriv_const', fractionalDerivative]
    rw [hz]
    exact iteratedDeriv_fun_const_zero
  have horder : fractionalDerivativeOrder (3 / 2) = 2 := by
    norm_num [fractionalDerivativeOrder]
    exact (Nat.floor_eq_iff (by norm_num)).mpr (by norm_num)
  have hhalf : ((2 : ℕ) : ℂ) - 3 / 2 = 1 / 2 := by norm_num
  have hI : fractionalIntegral (1 / 2) (fun _ : ℝ => (1 : ℂ)) =ᶠ[𝓝 (1 : ℝ)]
      (fun x : ℝ => (Complex.Gamma (3 / 2))⁻¹ * (x : ℂ) ^ (1 / 2 : ℂ)) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with x hx
    have h := fractionalIntegral_cpow (α := 1 / 2) (μ := 0) (by norm_num) (by norm_num) hx
    norm_num at h
    convert h using 1 <;> norm_num
  have hD : deriv (fun x : ℝ => (x : ℂ) ^ (1 / 2 : ℂ)) =ᶠ[𝓝 (1 : ℝ)]
      (fun x : ℝ => (1 / 2 : ℂ) * (x : ℂ) ^ (-(1 / 2) : ℂ)) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with x hx
    rw [Complex.deriv_ofReal_cpow_const hx.ne' (by norm_num)]
    norm_num
  have hDD : iteratedDeriv 2 (fun x : ℝ => (x : ℂ) ^ (1 / 2 : ℂ)) 1 = -(1 / 4 : ℂ) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one,
      hD.deriv_eq]
    have h := (hasDerivAt_ofReal_cpow_const (x := (1 : ℝ)) (by norm_num)
      (r := -(1 / 2 : ℂ)) (by norm_num)).const_mul (1 / 2 : ℂ)
    convert h.deriv using 1 <;> norm_num
  rw [hzero, fractionalDerivative, horder, hhalf, hI.iteratedDeriv_eq,
    iteratedDeriv_const_mul_field, hDD]
  exact Ne.symm (mul_ne_zero (inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos
    (s := (3 / 2 : ℂ)) (by norm_num))) (by norm_num))

end DLMF.AlgebraicAnalytic
