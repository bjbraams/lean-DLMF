/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Rotating the ray of integration

Let `f` be holomorphic on the closed sector between the rays `arg t = 0` and `arg t = α`
(origin excluded), with an integrable singularity `O(|t|^{σ-1})`, `σ > 0`, at the origin and
exponential decay at infinity, uniformly in the sector. Then

`∫₀^∞ f(r) dr = e^{iα} ∫₀^∞ f(r e^{iα}) dr`.

The proof applies Cauchy's theorem for rectangles (`Complex.integral_boundary_rect_eq_zero_of_
differentiableOn`) to `w ↦ f(e^w) e^w` on `[log ε, log R] × [0, α]` and lets `ε → 0`, `R → ∞`.
This is the contour rotation used with Watson's lemma (Temme, *Special Functions*, §2.2).

## Main results

* `integrableOn_ray_of_bounds`: integrability along each ray of the sector.
* `integral_Ioi_eq_exp_mul_integral_Ioi_rotate`: the rotation formula.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Complex

open scoped Topology Interval

namespace Complex

variable {f : ℂ → ℂ} {α σ κ C : ℝ}

/-- Integrability of `r ↦ f(r e^{iy})` on `(0, ∞)` from the bounds at `0` and `∞`. -/
lemma integrableOn_ray_of_bounds (hσ : 0 < σ) (hκ : 0 < κ) {y : ℝ}
    (hc : ∀ r : ℝ, 0 < r → ContinuousAt (fun r : ℝ => f (r * exp (y * I))) r)
    (h0 : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖f (r * exp (y * I))‖ ≤ C * r ^ (σ - 1))
    (hinf : ∀ r : ℝ, 1 ≤ r → ‖f (r * exp (y * I))‖ ≤ C * Real.exp (-κ * r)) :
    IntegrableOn (fun r : ℝ => f (r * exp (y * I))) (Ioi 0) := by
  have hcont : ContinuousOn (fun r : ℝ => f (r * exp (y * I))) (Ioi 0) :=
    fun r hr => (hc r hr).continuousWithinAt
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · have hmaj : IntegrableOn (fun r : ℝ => C * r ^ (σ - 1)) (Ioc 0 1) :=
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < σ - 1)).1).const_mul C
    refine hmaj.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Eventually.of_forall fun r hr => h0 r hr.1 hr.2)
  · have hmaj : IntegrableOn (fun r : ℝ => C * Real.exp (-κ * r)) (Ioi 1) :=
      (exp_neg_integrableOn_Ioi 1 hκ).const_mul C
    refine hmaj.mono' ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun r hr => hinf r (le_of_lt hr))

lemma exp_ofReal_add_mul_I (x y : ℝ) : exp ((x : ℂ) + y * I) = (Real.exp x : ℂ) * exp (y * I) := by
  rw [exp_add, ofReal_exp]

/-- The rectangle identity behind the rotation formula, for `0 < ε` and `0 < R`. -/
lemma integral_sub_exp_mul_integral_rotate {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (hd : ∀ r : ℝ, 0 < r → ∀ y ∈ [[0, α]], DifferentiableAt ℂ f (r * exp (y * I))) :
    (∫ r in ε..R, f r) - exp (α * I) * ∫ r in ε..R, f (r * exp (α * I)) =
      -(I * ∫ y in (0 : ℝ)..α, f (R * exp (y * I)) * (R * exp (y * I))) +
        I * ∫ y in (0 : ℝ)..α, f (ε * exp (y * I)) * (ε * exp (y * I)) := by
  set g : ℂ → ℂ := fun w => f (exp w) * exp w with hg
  have hgd : ∀ w : ℂ, w.im ∈ [[0, α]] → DifferentiableAt ℂ g w := by
    intro w hw
    have hew : exp w = (Real.exp w.re : ℂ) * exp (w.im * I) := by
      conv_lhs => rw [← re_add_im w]
      exact exp_ofReal_add_mul_I _ _
    have := hd (Real.exp w.re) (Real.exp_pos _) w.im hw
    rw [← hew] at this
    exact (this.comp w differentiableAt_exp).mul differentiableAt_exp
  have hrect := integral_boundary_rect_eq_zero_of_differentiableOn g
    (Real.log ε : ℂ) ((Real.log R : ℂ) + α * I) (fun w hw => by
      rw [mem_reProdIm] at hw
      have h2 := hw.2
      simp only [ofReal_im, add_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add] at h2
      exact (hgd w h2).differentiableWithinAt)
  simp only [ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im, mul_zero,
    mul_one, sub_zero, add_zero, zero_add, smul_eq_mul] at hrect
  -- the horizontal sides are the two ray integrals
  have hsub : ∀ y ∈ [[0, α]], ∫ x in (Real.log ε)..(Real.log R), g (x + y * I) =
      exp (y * I) * ∫ r in ε..R, f (r * exp (y * I)) := by
    intro y hy
    have hG : ContinuousOn (fun r : ℝ => f (r * exp (y * I)))
        (Real.exp '' [[Real.log ε, Real.log R]]) := by
      rintro _ ⟨x, -, rfl⟩
      have h1 : ContinuousAt (fun r : ℝ => (r : ℂ) * exp (y * I)) (Real.exp x) :=
        (by fun_prop : Continuous fun r : ℝ => (r : ℂ) * exp (y * I)).continuousAt
      exact (ContinuousAt.comp (g := f) (f := fun r : ℝ => (r : ℂ) * exp (y * I)) (x := Real.exp x)
        (hd _ (Real.exp_pos x) y hy).continuousAt h1
        ).continuousWithinAt
    have h := intervalIntegral.integral_deriv_smul_comp' (f := Real.exp) (f' := Real.exp)
      (g := fun r : ℝ => f (r * exp (y * I))) (a := Real.log ε) (b := Real.log R)
      (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn hG
    rw [Real.exp_log hε, Real.exp_log hR] at h
    rw [← h, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hg, Function.comp_apply, exp_ofReal_add_mul_I, Complex.real_smul]
    ring
  have h0 := hsub 0 left_mem_uIcc
  have hα := hsub α right_mem_uIcc
  -- the vertical sides
  have hvert : ∀ ρ : ℝ, 0 < ρ → ∫ y in (0 : ℝ)..α, g (Real.log ρ + y * I) =
      ∫ y in (0 : ℝ)..α, f (ρ * exp (y * I)) * (ρ * exp (y * I)) := fun ρ hρ =>
    intervalIntegral.integral_congr fun y _ => by
      simp only [hg, exp_ofReal_add_mul_I, Real.exp_log hρ]
  rw [h0, hα, hvert R hR, hvert ε hε] at hrect
  simp only [ofReal_zero, zero_mul, exp_zero, mul_one, one_mul] at hrect
  linear_combination hrect

/-- `∫_{1/n}^{n} g → ∫₀^∞ g` for `g` integrable on `(0, ∞)`. -/
lemma tendsto_integral_recip_nat_nat {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) :
    Tendsto (fun n : ℕ => ∫ r in (1 / (n + 1 : ℝ))..(n + 1), g r) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), g r)) := by
  have h1 : Tendsto (fun n : ℕ => ∫ r in (0 : ℝ)..(n + 1), g r) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), g r)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hg
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hI1 : IntegrableOn g (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one, integrableOn_Icc_iff_integrableOn_Ioc]
    exact hg.mono_set Ioc_subset_Ioi_self
  have hprim := intervalIntegral.continuousOn_primitive_interval hI1
  have h2 : Tendsto (fun n : ℕ => ∫ r in (0 : ℝ)..(1 / (n + 1 : ℝ)), g r) atTop (𝓝 0) := by
    have hc := (hprim 0 left_mem_uIcc).tendsto
    simp only [intervalIntegral.integral_same] at hc
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[uIcc 0 1] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n => ?_⟩
      rw [uIcc_of_le zero_le_one]
      exact ⟨by positivity, by rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]⟩
    exact hc.comp ht
  have h := h1.sub h2
  rw [sub_zero] at h
  refine h.congr fun n => ?_
  have hn : IntervalIntegrable g volume 0 (n + 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr
      (hg.mono_set Ioc_subset_Ioi_self)
  have hn' : IntervalIntegrable g volume 0 (1 / (n + 1 : ℝ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr
      (hg.mono_set Ioc_subset_Ioi_self)
  rw [intervalIntegral.integral_interval_sub_left hn hn']

/-- **Rotation of the ray of integration.** If `f` is holomorphic at every point `r e^{iy}`,
`r > 0`, `y` between `0` and `α`, with `|f(r e^{iy})| ≤ C r^{σ-1}` for `r ≤ 1` (`σ > 0`) and
`|f(r e^{iy})| ≤ C e^{-κ r}` for `r ≥ 1` (`κ > 0`), then
`∫₀^∞ f(r) dr = e^{iα} ∫₀^∞ f(r e^{iα}) dr`. -/
theorem integral_Ioi_eq_exp_mul_integral_Ioi_rotate (hσ : 0 < σ) (hκ : 0 < κ)
    (hd : ∀ r : ℝ, 0 < r → ∀ y ∈ [[0, α]], DifferentiableAt ℂ f (r * exp (y * I)))
    (h0 : ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ y ∈ [[0, α]], ‖f (r * exp (y * I))‖ ≤ C * r ^ (σ - 1))
    (hinf : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ [[0, α]], ‖f (r * exp (y * I))‖ ≤ C * Real.exp (-κ * r)) :
    ∫ r in Ioi (0 : ℝ), f r = exp (α * I) * ∫ r in Ioi (0 : ℝ), f (r * exp (α * I)) := by
  have hray : ∀ y ∈ [[0, α]], IntegrableOn (fun r : ℝ => f (r * exp (y * I))) (Ioi 0) :=
    fun y hy => integrableOn_ray_of_bounds hσ hκ
      (fun r hr => ContinuousAt.comp (g := f) (f := fun r : ℝ => (r : ℂ) * exp (y * I))
        (hd r hr y hy).continuousAt
        (by fun_prop : Continuous fun r : ℝ => (r : ℂ) * exp (y * I)).continuousAt)
      (fun r hr hr1 => h0 r hr hr1 y hy) (fun r hr => hinf r hr y hy)
  have hray0 : IntegrableOn (fun r : ℝ => f r) (Ioi 0) := by
    simpa using hray 0 left_mem_uIcc
  have hL := tendsto_integral_recip_nat_nat hray0
  have hR := (tendsto_integral_recip_nat_nat (hray α right_mem_uIcc)).const_mul (exp (α * I))
  -- the vertical sides vanish in the limit
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hinf 1 le_rfl 0 left_mem_uIcc)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hside : ∀ ρ : ℝ, 0 < ρ → ∀ B : ℝ, (∀ y ∈ [[0, α]], ‖f (ρ * exp (y * I))‖ ≤ B) →
      ‖I * ∫ y in (0 : ℝ)..α, f (ρ * exp (y * I)) * (ρ * exp (y * I))‖ ≤ B * ρ * |α| := by
    intro ρ hρ B hB
    rw [norm_mul, norm_I, one_mul]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := α) (C := B * ρ)
      (f := fun y : ℝ => f (ρ * exp (y * I)) * (ρ * exp (y * I))) fun y hy => by
        rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hρ.le, norm_exp_ofReal_mul_I,
          mul_one]
        exact mul_le_mul_of_nonneg_right (hB y (uIoc_subset_uIcc hy)) hρ.le
    rwa [sub_zero] at this
  have hD : Tendsto (fun n : ℕ => (∫ r in (1 / (n + 1 : ℝ))..(n + 1), f r) -
      exp (α * I) * ∫ r in (1 / (n + 1 : ℝ))..(n + 1), f (r * exp (α * I))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n : ℕ => C * Real.exp (-κ * (n + 1)) * (n + 1) * |α| +
      C * (1 / (n + 1 : ℝ)) ^ (σ - 1) * (1 / (n + 1 : ℝ)) * |α|) (fun n => ?_) ?_
    · have hn1 : (0 : ℝ) < n + 1 := by positivity
      rw [integral_sub_exp_mul_integral_rotate (by positivity) hn1 hd]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_neg]
        exact hside _ hn1 _ fun y hy => hinf _ (by linarith [n.cast_nonneg (α := ℝ)]) y hy
      · exact hside _ (by positivity) _ fun y hy => h0 _ (by positivity)
          (by rw [div_le_one hn1]; linarith [n.cast_nonneg (α := ℝ)]) y hy
    · have hA : Tendsto (fun n : ℕ => C * Real.exp (-κ * (n + 1)) * (n + 1) * |α|) atTop (𝓝 0) := by
        have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 κ hκ).comp
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
        have h2 := (h1.const_mul C).mul_const |α|
        simp only [mul_zero, zero_mul] at h2
        refine h2.congr fun n => ?_
        simp only [Function.comp_apply, Real.rpow_one]
        ring
      have hB : Tendsto (fun n : ℕ => C * (1 / (n + 1 : ℝ)) ^ (σ - 1) * (1 / (n + 1 : ℝ)) * |α|)
          atTop (𝓝 0) := by
        have h1 := ((Real.continuousAt_rpow_const 0 σ (Or.inr hσ.le)).tendsto.comp
          tendsto_one_div_add_atTop_nhds_zero_nat)
        rw [Real.zero_rpow hσ.ne'] at h1
        have h2 := (h1.const_mul C).mul_const |α|
        simp only [mul_zero, zero_mul] at h2
        refine h2.congr fun n => ?_
        have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
        simp only [Function.comp_apply]
        have hq : (1 / (n + 1 : ℝ)) ^ (σ - 1) * (1 / (n + 1 : ℝ)) = (1 / (n + 1 : ℝ)) ^ σ := by
          rw [← Real.rpow_add_one hpos.ne', sub_add_cancel]
        rw [mul_assoc C _ (1 / (n + 1 : ℝ)), hq]
      simpa using hA.add hB
  have h := hL.sub hR
  rw [← sub_eq_zero]
  exact tendsto_nhds_unique h hD

end Complex
