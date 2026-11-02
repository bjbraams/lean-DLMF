/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Distributional.Basic
public import TauCeti.Analysis.SpecialFunctions.Beta
public import DLMF.Gamma.IntegralRepresentations.FrullaniAndMoments
public import DLMF.Gamma.Polygamma
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Fractional integrals and regularization (DLMF §2.6(iii)–(iv))

Riemann–Liouville integrals and convolutions in the algebra `K⁺`, expansions of fractional
integrals with exact remainder, and the asymptotics of Mellin convolution integrals.

## Main results

* `riemannLiouvilleIntegral_eq_convolution`: the Riemann–Liouville integral as a convolution
  (DLMF 2.6.35).
* `integrableOn_powKernel_mul_rpow_iff`: DLMF 2.6.36.
* `halfLineConvolution_comm`, `kPlusPairing_convolution_congr`: the convolution algebra `K⁺`
  (DLMF 2.6.37).
* `kPlusPairing_powKernel_conv_delta`, `kPlusPairing_powKernel_conv_rpow`,
  `kPlusPairing_powKernel_conv_log`: the convolution identities 2.6.38–2.6.40.
* `riemannLiouvilleIntegral_eq_of_lt_one`, `riemannLiouvilleIntegral_eq_of_eq_one`: expansions
  of `I^μ f(x)` with exact remainder (DLMF 2.6.43–2.6.47).
* `stieltjesRemainder_rpowDivOneAddExample`, `isMellinContinuation_rpowDivOneAddExample`,
  `riemannLiouvilleIntegral_exampleF`, `norm_fractionalRemainder_exampleF_le`: the example
  2.6.48–2.6.53.
* `mul_comp_mul_eq_expansion`: the product expansion 2.6.57.
* `regularized_integral_rpow_eq_zero`: the regularization 2.6.59 of `∫₀^∞ t^λ dt`.
* `mellin_continuation_eq_mellin_remainder`, `mellinConvolutionIntegral_eq`: DLMF 2.6.60,
  2.6.62.

## Implementation notes

Elements `Dⁿ f` of `K⁺` are represented by pairs `(n, f)` and act on smooth compactly
supported test functions through `kPlusPairing n f φ = (-1)ⁿ ∫₀^∞ f φ^{(n)}`; the distributions
`t^λ` are `tPowPairing λ` (2.6.12–2.6.14) and `δ^{(s-1)} = D^s H` is the pair `(s, 1)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Real Filter Asymptotics Finset
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- DLMF 2.6.35: `I^μ f(x) = Γ(μ)⁻¹ (t^{μ-1} ∗ f)(x)`. -/
@[dlmf 2.6.E35]
theorem riemannLiouvilleIntegral_eq_convolution (μ : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    riemannLiouvilleIntegral μ f x =
      (Real.Gamma μ : ℂ)⁻¹ * halfLineConvolution (rpowKernel μ) f x := rfl

/-- DLMF 2.6.36: for `x > 0`, `μ > 0`, `0 < α ≤ 1` and `s = 0, 1, 2, …`, the convolution
integral `∫₀^x (x-t)^{μ-1} t^{-s-α} dt` exists in the usual (Lebesgue) sense exactly when
`s = 0` and `α < 1`. -/
@[dlmf 2.6.E36]
theorem integrableOn_powKernel_mul_rpow_iff {x μ α : ℝ} (hx : 0 < x) (hμ : 0 < μ) (hα : 0 < α)
    (s : ℕ) :
    IntegrableOn (fun t : ℝ => (x - t) ^ (μ - 1) * t ^ (-(s : ℝ) - α)) (Ioo 0 x) ↔
      s = 0 ∧ α < 1 := by
  let F : ℝ → ℝ := fun t => (x - t) ^ (μ - 1) * t ^ (-(s : ℝ) - α)
  have hscale : IntegrableOn F (Ioo 0 x) ↔
      IntegrableOn (fun t => F (x * t)) (Ioo 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le,
      ← IntervalIntegrable.comp_mul_left_iff hx.ne',
      zero_div, div_self hx.ne', intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  change IntegrableOn F (Ioo 0 x) ↔ _
  rw [hscale]
  have heq : EqOn (fun t => F (x * t))
      (fun t : ℝ => (x ^ (μ - 1) * x ^ (-(s : ℝ) - α)) *
        (t ^ ((1 - (s : ℝ) - α) - 1) * (1 - t) ^ (μ - 1))) (Ioo 0 1) := by
    intro t ht
    have ht1 : t < 1 := ht.2
    dsimp [F]
    rw [show x - x * t = x * (1 - t) by ring,
      Real.mul_rpow hx.le (by linarith : 0 ≤ 1 - t), Real.mul_rpow hx.le ht.1.le]
    rw [show 1 - (s : ℝ) - α - 1 = -(s : ℝ) - α by ring]
    ring
  rw [integrableOn_congr_fun heq measurableSet_Ioo, IntegrableOn,
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
      (mul_ne_zero (Real.rpow_pos_of_pos hx _).ne'
        (Real.rpow_pos_of_pos hx _).ne')), ← IntegrableOn,
    TauCeti.integrableOn_rpow_mul_one_sub_rpow_iff]
  constructor
  · rintro ⟨h, _⟩
    have hs : s = 0 := by
      by_contra hs
      have hs' : (1 : ℝ) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs
      linarith
    refine ⟨hs, ?_⟩
    simp only [hs, Nat.cast_zero, sub_zero] at h
    linarith
  · rintro ⟨rfl, hα'⟩
    exact ⟨by simpa using hα', hμ⟩

/-- DLMF 2.6.iii: the convolution of `K⁺` is commutative on representatives,
`f ∗ g = g ∗ f`. -/
@[dlmf 2.6.iii]
theorem halfLineConvolution_comm (f g : ℝ → ℂ) (x : ℝ) :
    halfLineConvolution f g x = halfLineConvolution g f x := by
  unfold halfLineConvolution
  have h := intervalIntegral.integral_comp_sub_left (fun u => g (x - u) * f u) x (a := 0)
    (b := x)
  simp only [sub_sub_cancel, sub_self, sub_zero] at h
  rw [← h]
  congr 1
  ext t
  ring

/-- DLMF 2.6.37: the convolution `Dⁿ f ∗ Dᵐ g = D^{n+m}(f ∗ g)` on `K⁺` is well defined: if
`(n, f)`, `(n', f')` represent the same distribution and `(m, g)`, `(m', g')` do, then so do
`(n + m, f ∗ g)` and `(n' + m', f' ∗ g')`. The representatives are locally integrable on
`[0, ∞)`; test functions are smooth with compact support. -/
@[dlmf 2.6.E37]
theorem kPlusPairing_convolution_congr {n n' m m' : ℕ} {f f' g g' : ℝ → ℂ}
    (hf : ∀ R, 0 < R → IntegrableOn f (Ioc 0 R)) (hf' : ∀ R, 0 < R → IntegrableOn f' (Ioc 0 R))
    (hg : ∀ R, 0 < R → IntegrableOn g (Ioc 0 R)) (hg' : ∀ R, 0 < R → IntegrableOn g' (Ioc 0 R))
    (hff : ∀ φ, IsCompactTest φ → kPlusPairing n f φ = kPlusPairing n' f' φ)
    (hgg : ∀ φ, IsCompactTest φ → kPlusPairing m g φ = kPlusPairing m' g' φ)
    {φ : ℝ → ℂ} (hφ : IsCompactTest φ) :
    kPlusPairing (n + m) (halfLineConvolution f g) φ =
      kPlusPairing (n' + m') (halfLineConvolution f' g') φ := by
  sorry

/-- DLMF 2.6.38: for `μ > 0`, `μ ≠ 1, 2, …` and `s ≥ 1`,
`t^{μ-1} ∗ δ^{(s-1)} = Γ(μ)/Γ(μ+1-s) · t^{μ-s}` as distributions on `t > 0`; here
`δ^{(s-1)} = D^s H` is represented by `(s, 1)` and `t^{μ-s}` is `tPowPairing (μ - s)`. -/
@[dlmf 2.6.E38]
theorem kPlusPairing_powKernel_conv_delta {μ : ℝ} (hμ : 0 < μ) (hμn : ∀ k : ℕ, μ ≠ k + 1)
    {s : ℕ} (hs : 1 ≤ s) {φ : ℝ → ℂ} (hφ : IsCompactTest φ) :
    kPlusPairing s (halfLineConvolution (rpowKernel μ) fun _ => 1) φ =
      (Real.Gamma μ / Real.Gamma (μ + 1 - s) : ℝ) * tPowPairing (μ - s) φ := by
  sorry

/-- DLMF 2.6.39: for `μ > 0`, `μ ≠ 1, 2, …`, `0 < α < 1` with `μ - α ∉ {0, 1, 2, …}`, and
`s = 0, 1, 2, …`, `t^{μ-1} ∗ t^{-s-α} = Γ(μ)Γ(1-s-α)/Γ(μ+1-s-α) · t^{μ-s-α}`, where
`t^{-s-α} = (-1)^s (α)_s⁻¹ D^s t^{-α}` (2.6.13). -/
@[dlmf 2.6.E39]
theorem kPlusPairing_powKernel_conv_rpow {μ α : ℝ} (hμ : 0 < μ) (hμn : ∀ k : ℕ, μ ≠ k + 1)
    (hα0 : 0 < α) (hα1 : α < 1) (hμα : ∀ k : ℕ, μ - α ≠ k) (s : ℕ) {φ : ℝ → ℂ}
    (hφ : IsCompactTest φ) :
    ((-1 : ℂ) ^ s * (((ascPochhammer ℝ s).eval α : ℝ) : ℂ)⁻¹) *
        kPlusPairing s (halfLineConvolution (rpowKernel μ)
          fun t => ((t ^ (-α) : ℝ) : ℂ)) φ =
      (Real.Gamma μ * Real.Gamma (1 - s - α) / Real.Gamma (μ + 1 - s - α) : ℝ) *
        tPowPairing (μ - s - α) φ := by
  sorry

/-- `0 ≤ 1 - v^μ ≤ max 1 μ · (1 - v)` for `0 ≤ v ≤ 1`, `μ > 0`. -/
private lemma one_sub_rpow_le {μ v : ℝ} (hμ : 0 < μ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ 1 - v ^ μ ∧ 1 - v ^ μ ≤ max 1 μ * (1 - v) := by
  refine ⟨by linarith [Real.rpow_le_one hv0 hv1 hμ.le], ?_⟩
  rcases le_total μ 1 with h | h
  · have : v ^ (1 : ℝ) ≤ v ^ μ := Real.rpow_le_rpow_of_exponent_ge' hv0 hv1 hμ.le h
    rw [Real.rpow_one] at this
    nlinarith [le_max_left 1 μ]
  · have hb := one_add_mul_self_le_rpow_one_add (s := v - 1) (by linarith) h
    rw [show 1 + (v - 1) = v by ring] at hb
    nlinarith [le_max_right 1 μ]

/-- `(1 - v^μ)/(1 - v)` is integrable on `(0, 1)`. -/
private lemma integrableOn_one_sub_rpow_div {μ : ℝ} (hμ : 0 < μ) :
    IntegrableOn (fun v : ℝ => (1 - v ^ μ) / (1 - v)) (Ioo 0 1) := by
  have hmeas : AEStronglyMeasurable (fun v : ℝ => (1 - v ^ μ) / (1 - v))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine ContinuousOn.aestronglyMeasurable (fun v hv => ?_) measurableSet_Ioo
    have h1 : 1 - v ≠ 0 := by linarith [hv.2]
    exact ((continuousAt_const.sub (Real.continuousAt_rpow_const _ _ (Or.inr hμ.le))).div
      (continuousAt_const.sub continuousAt_id) h1).continuousWithinAt
  have hbd : ∀ᵐ v ∂(volume.restrict (Ioo (0 : ℝ) 1)), ‖(1 - v ^ μ) / (1 - v)‖ ≤ max 1 μ := by
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun v hv => ?_)
    obtain ⟨h0, h1⟩ := one_sub_rpow_le hμ hv.1.le hv.2.le
    have hp : 0 < 1 - v := by linarith [hv.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 hp.le), div_le_iff₀ hp]
    exact h1
  exact (integrableOn_const (C := max 1 μ) measure_Ioo_lt_top.ne).mono' hmeas hbd

/-- `v^{μ-1} ln(1 - v)` is integrable on `(0, 1)` for `μ > 0`. -/
private lemma integrableOn_rpow_mul_log_one_sub {μ : ℝ} (hμ : 0 < μ) :
    IntegrableOn (fun v : ℝ => v ^ (μ - 1) * Real.log (1 - v)) (Ioo 0 1) := by
  have hB : IntegrableOn (fun v : ℝ => v ^ (μ - 1) * (1 - v) ^ ((1 / 2 : ℝ) - 1)) (Ioo 0 1) :=
    TauCeti.integrableOn_rpow_mul_one_sub_rpow_iff.mpr ⟨hμ, by norm_num⟩
  have hmeas : AEStronglyMeasurable (fun v : ℝ => v ^ (μ - 1) * Real.log (1 - v))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine ContinuousOn.aestronglyMeasurable (fun v hv => ?_) measurableSet_Ioo
    have h1 : 1 - v ≠ 0 := by linarith [hv.2]
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hv.1.ne')).mul
      ((continuousAt_const.sub continuousAt_id).log h1)).continuousWithinAt
  refine (hB.const_mul 2).mono' hmeas ((ae_restrict_iff' measurableSet_Ioo).mpr
    (Eventually.of_forall fun v hv => ?_))
  · have hp : 0 < 1 - v := by linarith [hv.2]
    have hlog : Real.log (1 - v) ≤ 0 := Real.log_nonpos hp.le (by linarith [hv.1])
    have hy := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hp (-(1 / 2 : ℝ)))
    rw [Real.log_rpow hp] at hy
    have hv' : 0 < v ^ (μ - 1) := Real.rpow_pos_of_pos hv.1 _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hv', abs_of_nonpos hlog]
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
    have : -Real.log (1 - v) ≤ 2 * (1 - v) ^ (-(1 / 2 : ℝ)) := by nlinarith
    nlinarith

/-- `∫₀¹ v^{μ-1} ln(1 - v) dv = -(ψ(μ+1) + γ)/μ`, by parts and DLMF 5.9.16. -/
private lemma integral_rpow_mul_log_one_sub {μ : ℝ} (hμ : 0 < μ) :
    ∫ v in (0 : ℝ)..1, v ^ (μ - 1) * Real.log (1 - v) =
      -(Gamma.Real.digamma (μ + 1) + Real.eulerMascheroniConstant) / μ := by
  set P : ℝ → ℝ := fun v => (v ^ μ - 1) * Real.log (1 - v) with hP
  set P' : ℝ → ℝ := fun v => μ * (v ^ (μ - 1) * Real.log (1 - v)) + (1 - v ^ μ) / (1 - v)
    with hP'
  have hI1 := integrableOn_rpow_mul_log_one_sub hμ
  have hI2 := integrableOn_one_sub_rpow_div hμ
  have hint : IntervalIntegrable P' volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact (hI1.const_mul μ).add hI2
  have hcont : ContinuousOn P (Icc 0 1) := by
    intro v hv
    rcases lt_or_eq_of_le hv.2 with h1 | h1
    · have h1' : 1 - v ≠ 0 := by linarith
      exact (((Real.continuousAt_rpow_const _ _ (Or.inr hμ.le)).sub continuousAt_const).mul
        ((continuousAt_const.sub continuousAt_id).log h1')).continuousWithinAt
    · subst h1
      have hP1 : P 1 = 0 := by simp [hP]
      rw [ContinuousWithinAt, hP1]
      have hlim : Tendsto (fun v : ℝ => max 1 μ * |(1 - v) * Real.log (1 - v)|)
          (𝓝[Icc 0 1] 1) (𝓝 0) := by
        have hc : Continuous fun v : ℝ => max 1 μ * |(1 - v) * Real.log (1 - v)| :=
          continuous_const.mul ((Real.continuous_mul_log.comp
            (continuous_const.sub continuous_id)).abs)
        have := hc.tendsto 1
        simp only [sub_self, Real.log_zero, mul_zero, abs_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with v hv
      obtain ⟨h0, hle⟩ := one_sub_rpow_le hμ hv.1 hv.2
      have hlog : Real.log (1 - v) ≤ 0 := Real.log_nonpos (by linarith [hv.2]) (by linarith [hv.1])
      simp only [hP, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg (by linarith [hv.2] : 0 ≤ 1 - v),
        abs_of_nonpos (by linarith : v ^ μ - 1 ≤ 0),
        abs_of_nonpos hlog]
      nlinarith
  have hderiv : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt P (P' v) v := by
    intro v hv
    have h1 : 1 - v ≠ 0 := by linarith [hv.2]
    have hd := ((Real.hasDerivAt_rpow_const (p := μ) (Or.inl hv.1.ne')).sub_const 1).mul
      (((hasDerivAt_id v).const_sub 1).log h1)
    have hfun : P = (fun x => x ^ μ - 1) * fun y => Real.log (1 - id y) := rfl
    rw [hfun]
    refine hd.congr_deriv ?_
    simp only [hP', id]
    field_simp
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
  have hP0 : P 0 = 0 := by simp [hP]
  have hP1 : P 1 = 0 := by simp [hP]
  rw [hP0, hP1, sub_zero] at hftc
  have hsplit : ∫ v in (0 : ℝ)..1, P' v =
      (μ * ∫ v in (0 : ℝ)..1, v ^ (μ - 1) * Real.log (1 - v)) +
      ∫ v in (0 : ℝ)..1, (1 - v ^ μ) / (1 - v) := by
    have h1 : IntervalIntegrable (fun v : ℝ => μ * (v ^ (μ - 1) * Real.log (1 - v)))
        volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]; exact hI1.const_mul μ
    have h2 : IntervalIntegrable (fun v : ℝ => (1 - v ^ μ) / (1 - v)) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]; exact hI2
    rw [hP', intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul]
  have hdig := (DLMF.Gamma.digamma_add_euler (x := μ + 1) (by linarith)).2
  rw [show μ + 1 - 1 = μ by ring] at hdig
  rw [hsplit, ← hdig] at hftc
  rw [eq_div_iff hμ.ne']
  linear_combination hftc

/-- `∫₀ˣ (x-t)^{μ-1} ln t dt = μ⁻¹ x^μ (ln x - γ - ψ(μ+1))`. -/
private lemma integral_rpow_sub_mul_log {μ : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : 0 < x) :
    ∫ t in (0 : ℝ)..x, (x - t) ^ (μ - 1) * Real.log t =
      μ⁻¹ * (x ^ μ * (Real.log x - Real.eulerMascheroniConstant - Gamma.Real.digamma (μ + 1))) := by
  have h1 := intervalIntegral.integral_comp_sub_left
    (fun t => (x - t) ^ (μ - 1) * Real.log t) x (a := 0) (b := x)
  simp only [sub_sub_cancel, sub_self, sub_zero] at h1
  rw [← h1]
  have h2 := intervalIntegral.integral_comp_mul_left
    (fun s => s ^ (μ - 1) * Real.log (x - s)) hx.ne' (a := 0) (b := 1)
  simp only [mul_zero, mul_one] at h2
  rw [show (∫ s in (0 : ℝ)..x, s ^ (μ - 1) * Real.log (x - s)) =
      x * ∫ v in (0 : ℝ)..1, (x * v) ^ (μ - 1) * Real.log (x - x * v) by
    rw [h2, smul_eq_mul, mul_inv_cancel_left₀ hx.ne']]
  have hcongr : ∫ v in (0 : ℝ)..1, (x * v) ^ (μ - 1) * Real.log (x - x * v) =
      ∫ v in (0 : ℝ)..1, x ^ (μ - 1) * (Real.log x * v ^ (μ - 1) +
        v ^ (μ - 1) * Real.log (1 - v)) := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
    have hp : 0 < 1 - v := by linarith [hv.2]
    rw [Real.mul_rpow hx.le hv.1.le, show x - x * v = x * (1 - v) by ring,
      Real.log_mul hx.ne' hp.ne']
    ring
  have hr : IntervalIntegrable (fun v : ℝ => v ^ (μ - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hl : IntervalIntegrable (fun v : ℝ => v ^ (μ - 1) * Real.log (1 - v)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact integrableOn_rpow_mul_log_one_sub hμ
  rw [hcongr, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hr.const_mul _) hl, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith)), integral_rpow_mul_log_one_sub hμ,
    show μ - 1 + 1 = μ by ring, Real.zero_rpow hμ.ne', Real.one_rpow,
    Real.rpow_sub_one hx.ne']
  field_simp
  ring

/-- The convolution behind DLMF 2.6.40, as an identity of functions:
`(t^{μ-1} ∗ ln t)(x) = μ⁻¹ x^μ (ln x - γ - ψ(μ+1))` for `x > 0`, `μ > 0`. -/
@[dlmf 2.6.E40]
theorem halfLineConvolution_powKernel_log {μ : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : 0 < x) :
    halfLineConvolution (rpowKernel μ) (fun t => (Real.log t : ℂ)) x =
      (μ : ℂ)⁻¹ * logRpowKernel μ x := by
  have h : halfLineConvolution (rpowKernel μ) (fun t => (Real.log t : ℂ)) x =
      ((∫ t in (0 : ℝ)..x, (x - t) ^ (μ - 1) * Real.log t : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp only [halfLineConvolution, rpowKernel, Complex.ofReal_mul]
  have hd := DLMF.Gamma.digamma_ofReal (x := μ + 1) (by linarith)
  push_cast at hd
  rw [h, integral_rpow_sub_mul_log hμ hx, logRpowKernel, hd]
  push_cast
  ring

/-- DLMF 2.6.40: for `μ > 0` and `s = 0, 1, 2, …`,
`t^{μ-1} ∗ t^{-s-1} = (-1)^s/(μ s!) · D^{s+1}(t^μ (ln t - γ - ψ(μ+1)))`, where
`t^{-s-1} = (-1)^s/s! · D^{s+1} ln t` (2.6.14). Stronger than DLMF: no condition `μ ∉ ℕ`. -/
@[dlmf 2.6.E40]
theorem kPlusPairing_powKernel_conv_log {μ : ℝ} (hμ : 0 < μ) (s : ℕ) (φ : ℝ → ℂ) :
    (-1 : ℂ) ^ s / (s.factorial : ℂ) *
        kPlusPairing (s + 1) (halfLineConvolution (rpowKernel μ)
          fun t => (Real.log t : ℂ)) φ =
      (-1 : ℂ) ^ s / ((μ : ℂ) * (s.factorial : ℂ)) * kPlusPairing (s + 1) (logRpowKernel μ) φ := by
  have h : ∫ t in Ioi (0 : ℝ), halfLineConvolution (rpowKernel μ)
        (fun t => (Real.log t : ℂ)) t * iteratedDeriv (s + 1) φ t =
      ∫ t in Ioi (0 : ℝ), (μ : ℂ)⁻¹ * (logRpowKernel μ t * iteratedDeriv (s + 1) φ t) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      rw [halfLineConvolution_powKernel_log hμ ht]; ring
  unfold kPlusPairing
  rw [h, integral_const_mul]
  have hμ0 : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  field_simp

/-- DLMF 2.6.45 (with 2.6.47; the function form of the distributional identity 2.6.43): for
`0 < α < 1`, `μ > 0`, `n ≥ 1` and `x > 0`,
`I^μ f(x) = ∑_{s<n} a_s Γ(1-s-α)/Γ(μ+1-s-α) x^{μ-s-α} - ∑_{s=1}^{n} c_s/Γ(μ+1-s) x^{μ-s}
  + x⁻ⁿ δ_n(x)`, with `c_s` as in 2.6.18. -/
@[dlmf 2.6.E45, dlmf 2.6.E43]
theorem riemannLiouvilleIntegral_eq_of_lt_one {f : ℝ → ℂ} {α : ℝ} {a : ℕ → ℂ}
    (hf : IsStieltjesExpansion f α a) (hα : α < 1) {M : ℂ → ℂ}
    (hM : IsMellinContinuation f α M) {μ : ℝ} (hμ : 0 < μ) {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : 0 < x) :
    riemannLiouvilleIntegral μ f x =
      ∑ s ∈ range n, a s * (Real.Gamma (1 - s - α) / Real.Gamma (μ + 1 - s - α) *
          x ^ (μ - s - α) : ℝ) -
        ∑ s ∈ Icc 1 n, stieltjesDeltaCoeff M s * (x ^ (μ - s) / Real.Gamma (μ + 1 - s) : ℝ) +
        ((x ^ n : ℝ) : ℂ)⁻¹ * fractionalRemainder μ (stieltjesRemainder f α a n) n x := by
  sorry

/-- DLMF 2.6.46 (with 2.6.47; the function form of 2.6.44): for `α = 1`, `μ > 0`, `n ≥ 1` and
`x > 0`,
`I^μ f(x) = ∑_{s<n} (-1)^s a_s/(s! Γ(μ+1)) (d/dx)^{s+1}(x^μ(ln x - γ - ψ(μ+1)))
  - ∑_{s=1}^{n} d_s/Γ(μ-s+1) x^{μ-s} + x⁻ⁿ δ_n(x)`, with `d_s` as in 2.6.21. -/
@[dlmf 2.6.E46, dlmf 2.6.E44]
theorem riemannLiouvilleIntegral_eq_of_eq_one {f : ℝ → ℂ} {a : ℕ → ℂ}
    (hf : IsStieltjesExpansion f 1 a) {M : ℂ → ℂ} (hM : IsMellinContinuation f 1 M) {μ : ℝ}
    (hμ : 0 < μ) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    riemannLiouvilleIntegral μ f x =
      ∑ s ∈ range n, (-1 : ℂ) ^ s * a s / ((s.factorial : ℂ) * Real.Gamma (μ + 1)) *
          iteratedDeriv (s + 1) (logRpowKernel μ) x -
        ∑ s ∈ range n, stieltjesLogDeltaCoeff M a s *
          (x ^ (μ - (s + 1)) / Real.Gamma (μ - s) : ℝ) +
        ((x ^ n : ℝ) : ℂ)⁻¹ * fractionalRemainder μ (stieltjesRemainder f 1 a n) n x := by
  sorry

/-! ### Example: `f(t) = t^{1-α}/(1+t)` -/

/-- DLMF 2.6.49–2.6.50: for `t > 0`,
`f(t) = ∑_{s<n} (-1)^s t^{-s-α} + (-1)ⁿ t^{1-n-α}/(1+t)`; so `a_s = (-1)^s` and
`f_n(t) = (-1)ⁿ t^{1-n-α}/(1+t)`. -/
@[dlmf 2.6.E49, dlmf 2.6.E50]
theorem stieltjesRemainder_rpowDivOneAddExample (α : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    stieltjesRemainder (rpowDivOneAddExample α) α (fun s => (-1 : ℂ) ^ s) n t =
      (-1 : ℂ) ^ n * ((t ^ (1 - n - α) / (1 + t) : ℝ) : ℂ) := by
  induction n with
  | zero => simp [stieltjesRemainder, rpowDivOneAddExample]
  | succ n ih =>
    have he : stieltjesRemainder (rpowDivOneAddExample α) α (fun s => (-1 : ℂ) ^ s) (n + 1) t =
        stieltjesRemainder (rpowDivOneAddExample α) α (fun s => (-1 : ℂ) ^ s) n t -
          (-1 : ℂ) ^ n * ((t ^ (-((n : ℝ) + α)) : ℝ) : ℂ) := by
      simp only [stieltjesRemainder, Finset.sum_range_succ]
      ring
    rw [he, ih, pow_succ]
    have hp : t ^ (1 - (n : ℝ) - α) = t * t ^ (-((n : ℝ) + α)) := by
      rw [show 1 - (n : ℝ) - α = 1 + (-((n : ℝ) + α)) by ring,
        Real.rpow_add ht, Real.rpow_one]
    have he' : (1 - ((n + 1 : ℕ) : ℝ) - α) = -((n : ℝ) + α) := by push_cast; ring
    rw [he', hp]
    push_cast
    have hden : (1 + (t : ℂ)) ≠ 0 := by exact_mod_cast (by linarith : (1 + t : ℝ) ≠ 0)
    field_simp [hden]
    ring

/-- DLMF 2.6.51: the Mellin transform of `f(t) = t^{1-α}/(1+t)`, `0 < α < 1`, continues to
`𝓜f(z) = π/sin(π(z+1-α))`, and at the integers `𝓜f(s) = (-1)^s π/sin(πα)`. -/
@[dlmf 2.6.E51]
theorem isMellinContinuation_rpowDivOneAddExample {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IsMellinContinuation (rpowDivOneAddExample α) α
        (fun z => π / Complex.sin (π * (z + 1 - α))) ∧
      ∀ s : ℕ, π / Complex.sin (π * ((s : ℂ) + 1 - α)) = (-1 : ℂ) ^ s * (π / Real.sin (π * α)) := by
  sorry

/-- DLMF 2.6.52 (with 2.6.48): for `0 < α < 1`, `μ > 0`, `n ≥ 1` and `x > 0`,
`I^μ f(x) = ∑_{s<n} (-1)^s Γ(1-s-α)/Γ(μ+1-s-α) x^{μ-s-α}
  - π/sin(πα) ∑_{s=1}^{n} x^{μ-s}/(Γ(μ+1-s) (s-1)!) + x⁻ⁿ δ_n(x)`
for `f(t) = t^{1-α}/(1+t)`. -/
@[dlmf 2.6.E52, dlmf 2.6.E48]
theorem riemannLiouvilleIntegral_exampleF {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {μ : ℝ}
    (hμ : 0 < μ) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    riemannLiouvilleIntegral μ (rpowDivOneAddExample α) x =
      ((∑ s ∈ range n, (-1) ^ s * (Real.Gamma (1 - s - α) / Real.Gamma (μ + 1 - s - α)) *
            x ^ (μ - s - α) -
          π / Real.sin (π * α) *
            ∑ s ∈ Icc 1 n,
              x ^ (μ - s) / (Real.Gamma (μ + 1 - s) * ((s - 1).factorial : ℝ)) : ℝ) : ℂ) +
        ((x ^ n : ℝ) : ℂ)⁻¹ *
          fractionalRemainder μ (fun t => (-1 : ℂ) ^ n * ((t ^ (1 - n - α) / (1 + t) : ℝ) : ℂ))
            n x := by
  sorry

/-- DLMF 2.6.53: the bound on the remainder of the example: for `x > 0`,
`|δ_n(x)| ≤ Γ(μ+1)Γ(1-α)/(Γ(μ+1-α)Γ(n+α)) ∑_{j=0}^{n} (n choose j) Γ(n+α-j)/|Γ(μ+1-j)|
  · x^{μ-α}`. -/
@[dlmf 2.6.E53]
theorem norm_fractionalRemainder_exampleF_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {μ : ℝ}
    (hμ : 0 < μ) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ‖fractionalRemainder μ (fun t => (-1 : ℂ) ^ n * ((t ^ (1 - n - α) / (1 + t) : ℝ) : ℂ)) n x‖ ≤
      Real.Gamma (μ + 1) * Real.Gamma (1 - α) / (Real.Gamma (μ + 1 - α) * Real.Gamma (n + α)) *
        ∑ j ∈ range (n + 1), (n.choose j : ℝ) * Real.Gamma (n + α - j) /
          |Real.Gamma (μ + 1 - j)| * x ^ (μ - α) := by
  sorry

/-! ### §2.6(iv) Regularization -/

/-- DLMF 2.6.57: the product of the expansions 2.6.55 and 2.6.56: for `x, t > 0`,
`f(t)h(xt) = ∑_{j,k<n} a_j b_k t^{j+α-1-k-β} x^{-k-β} + ∑_{j<n} a_j t^{j+α-1} h_n(xt)
  + ∑_{k<n} b_k x^{-k-β} t^{-k-β} f_n(t) + f_n(t) h_n(xt)`,
where `f_n = f - ∑_{j<n} a_j t^{j+α-1}` and `h_n = h - ∑_{k<n} b_k t^{-k-β}`. -/
@[dlmf 2.6.E57, dlmf 2.6.E55, dlmf 2.6.E56]
theorem mul_comp_mul_eq_expansion (f h : ℝ → ℂ) (a b : ℕ → ℂ) (α β : ℝ) (n : ℕ) {x t : ℝ}
    (hx : 0 < x) (ht : 0 < t) :
    let fn : ℝ → ℂ := fun t => f t - ∑ j ∈ range n, a j * ((t ^ ((j : ℝ) + α - 1) : ℝ) : ℂ)
    let hn : ℝ → ℂ := fun t => h t - ∑ k ∈ range n, b k * ((t ^ (-(k : ℝ) - β) : ℝ) : ℂ)
    f t * h (x * t) =
      ∑ j ∈ range n, ∑ k ∈ range n, a j * b k *
          ((t ^ ((j : ℝ) + α - 1 - k - β) * x ^ (-(k : ℝ) - β) : ℝ) : ℂ) +
        ∑ j ∈ range n, a j * ((t ^ ((j : ℝ) + α - 1) : ℝ) : ℂ) * hn (x * t) +
        ∑ k ∈ range n, b k * ((x ^ (-(k : ℝ) - β) * t ^ (-(k : ℝ) - β) : ℝ) : ℂ) * fn t +
        fn t * hn (x * t) := by
  intro fn hn
  set A : ℂ := ∑ j ∈ range n, a j * ((t ^ ((j : ℝ) + α - 1) : ℝ) : ℂ) with hA
  set B : ℂ := ∑ k ∈ range n, b k * (((x * t) ^ (-(k : ℝ) - β) : ℝ) : ℂ) with hB
  have hf : f t = A + fn t := by simp only [fn, hA]; ring
  have hh : h (x * t) = B + hn (x * t) := by simp only [hn, hB]; ring
  have hxt : ∀ k : ℕ, (x * t) ^ (-(k : ℝ) - β) = x ^ (-(k : ℝ) - β) * t ^ (-(k : ℝ) - β) :=
    fun k => Real.mul_rpow hx.le ht.le
  have hAB : A * B = ∑ j ∈ range n, ∑ k ∈ range n, a j * b k *
      ((t ^ ((j : ℝ) + α - 1 - k - β) * x ^ (-(k : ℝ) - β) : ℝ) : ℂ) := by
    rw [hA, hB, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hxt k, show (j : ℝ) + α - 1 - k - β = ((j : ℝ) + α - 1) + (-(k : ℝ) - β) by ring,
      Real.rpow_add ht]
    push_cast
    ring
  have hAh : A * hn (x * t) = ∑ j ∈ range n, a j * ((t ^ ((j : ℝ) + α - 1) : ℝ) : ℂ) *
      hn (x * t) := by rw [hA, Finset.sum_mul]
  have hBf : B * fn t = ∑ k ∈ range n, b k * ((x ^ (-(k : ℝ) - β) * t ^ (-(k : ℝ) - β) : ℝ) : ℂ) *
      fn t := by
    rw [hB, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hxt k]
  rw [hf, hh, ← hAB, ← hAh, ← hBf]
  ring

/-- DLMF 2.6.59: the regularized value `∫₀^∞ t^λ dt = 0`. The integral splits as
`∫₀^1 t^λ dt = 1/(λ+1)` (convergent for `ℜλ > -1`) and `∫₁^∞ t^λ dt = -1/(λ+1)` (convergent
for `ℜλ < -1`); the analytic continuations of the two halves to `λ ≠ -1` cancel. -/
@[dlmf 2.6.E59]
theorem regularized_integral_rpow_eq_zero :
    (∀ lam : ℂ, -1 < lam.re → ∫ t in (0 : ℝ)..1, (t : ℂ) ^ lam = 1 / (lam + 1)) ∧
      (∀ lam : ℂ, lam.re < -1 → ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ lam = -1 / (lam + 1)) ∧
      ∀ lam : ℂ, 1 / (lam + 1) + -1 / (lam + 1) = 0 := by
  refine ⟨fun lam hlam => ?_, fun lam hlam => ?_, fun lam => by ring⟩
  · have hne : lam + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    rw [integral_cpow (Or.inl hlam)]
    have h0 : (0 : ℂ) ^ (lam + 1) = 0 := by
      rw [Complex.zero_cpow hne]
    simp [h0]
  · rw [integral_Ioi_cpow_of_lt hlam one_pos]
    simp

/-- DLMF 2.6.60: with the hypotheses of 2.6.55 (`f_n(t) = O(t^{n+α-1})` as `t → 0+`), the
continued Mellin transform of `f` equals the Mellin transform of `f_n` in the strip
`1 - n - α < ℜz < 2 - n - α` where the latter converges: `𝓜f(z) = 𝓜f_n(z)`. -/
@[dlmf 2.6.E60, dlmf 2.6.E55]
theorem mellin_continuation_eq_mellin_remainder {f : ℝ → ℂ} {a : ℕ → ℂ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    (hloc : ∀ R, 0 < R → IntegrableOn f (Ioc 0 R))
    (hfn : (fun t : ℝ => f t - ∑ j ∈ range n, a j * ((t ^ ((j : ℝ) + α - 1) : ℝ) : ℂ))
      =O[𝓝[>] 0] (fun t : ℝ => t ^ ((n : ℝ) + α - 1)))
    {M : ℂ → ℂ} {U : Set ℂ} (hM : IsMellinContinuationOn f M U) {z : ℂ} (hz : z ∈ U)
    (hz1 : 1 - n - α < z.re) (hz2 : z.re < 2 - n - α)
    (hconv : MellinConvergent
      (fun t : ℝ => f t - ∑ j ∈ range n, a j * ((t ^ ((j : ℝ) + α - 1) : ℝ) : ℂ)) z) :
    M z = mellin (fun t : ℝ => f t - ∑ j ∈ range n, a j * ((t ^ ((j : ℝ) + α - 1) : ℝ) : ℂ)) z := by
  sorry

/-- DLMF 2.6.62: for `α ≠ β`, under 2.6.55–2.6.56 with continued Mellin transforms `Mh` of
`h` (to a domain containing `j + α`, `j < n`) and `Mf` of `f` (containing `1 - k - β`,
`k < n`), `I(x) = ∑_{j<n} a_j 𝓜h(j+α) x^{-j-α} + ∑_{k<n} b_k 𝓜f(1-k-β) x^{-k-β} + δ_n(x)`
for `x > 0`, with `δ_n(x) = ∫₀^∞ f_n(t) h_n(xt) dt`. -/
@[dlmf 2.6.E62]
theorem mellinConvolutionIntegral_eq {f h : ℝ → ℂ} {a b : ℕ → ℂ} {α β : ℝ} (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hαβ : α ≠ β) {n : ℕ} (hn : 1 ≤ n)
    (hfn : (fun t : ℝ => f t - ∑ j ∈ range n, a j * ((t ^ ((j : ℝ) + α - 1) : ℝ) : ℂ))
      =O[𝓝[>] 0] (fun t : ℝ => t ^ ((n : ℝ) + α - 1)))
    (hhn : (fun t : ℝ => h t - ∑ k ∈ range n, b k * ((t ^ (-(k : ℝ) - β) : ℝ) : ℂ))
      =O[atTop] (fun t : ℝ => t ^ (-(n : ℝ) - β)))
    (hfloc : ∀ R, 0 < R → IntegrableOn f (Ioc 0 R)) (hhloc : ∀ R, 0 < R → IntegrableOn h (Ioc 0 R))
    {Mf Mh : ℂ → ℂ} {Uf Uh : Set ℂ} (hMf : IsMellinContinuationOn f Mf Uf)
    (hMh : IsMellinContinuationOn h Mh Uh) (hUf : ∀ k < n, (1 - k - β : ℂ) ∈ Uf)
    (hUh : ∀ j < n, ((j : ℂ) + α) ∈ Uh) {x : ℝ} (hx : 0 < x) :
    mellinConvolutionIntegral f h x =
      ∑ j ∈ range n, a j * Mh ((j : ℂ) + α) * ((x ^ (-(j : ℝ) - α) : ℝ) : ℂ) +
        ∑ k ∈ range n, b k * Mf (1 - k - β) * ((x ^ (-(k : ℝ) - β) : ℝ) : ℂ) +
        ∫ t in Ioi (0 : ℝ),
          (f t - ∑ j ∈ range n, a j * ((t ^ ((j : ℝ) + α - 1) : ℝ) : ℂ)) *
            (h (x * t) - ∑ k ∈ range n, b k * (((x * t) ^ (-(k : ℝ) - β) : ℝ) : ℂ)) := by
  sorry

end DLMF.AsymptoticApproximations
