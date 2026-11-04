/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy

/-!
# Keyhole integrals around the negative real axis

For `g` holomorphic on a punctured disk `0 < |z| < R` and `a ∈ ℂ`, the keyhole (Hankel-type) loop
integral of `z^a g(z)` of radius `0 < δ < R` around the negative real axis is
`(e^{-iπa} - e^{iπa}) ∫_δ^∞ x^a g(-x) dx + ∫_{-π}^{π} δ^a e^{iaθ} g(δe^{iθ}) iδe^{iθ} dθ`:
the two edges of the cut `(-∞, -δ]` and the circle `|z| = δ`, with `z^a` taking the boundary
values `x^a e^{∓iπa}` on the edges.

## Main results

* `Complex.exp_ne_one_of_norm_lt`, `Complex.half_norm_le_norm_exp_sub_one`: elementary facts on
  `e^z - 1` near `0`, for the kernels `1/(e^{-z} ∓ 1)`.

* `Complex.keyholeCircleIntegral_sub`: the circle integrals of radii `δ₁ ≤ δ₂` differ by
  `(e^{-iπa} - e^{iπa}) ∫_{δ₁}^{δ₂} x^a g(-x) dx`, so the keyhole integral does not depend on
  `δ`.
* `Complex.keyholeIntegral_eq_mul_integral_Ioi`: for `Re a > 0` and `g(z) = O(1/z)` at `0` the
  keyhole integral equals `(e^{-iπa} - e^{iπa}) ∫_0^∞ x^a g(-x) dx`.
* `Complex.differentiable_keyholeIntegral`: for `g` decaying exponentially along the negative real
  axis the keyhole integral is an entire function of `a`.

## Implementation notes

In the coordinate `w = log z` the keyhole becomes three sides of the rectangle
`[log δ₁, log δ₂] × [-π, π]`, and Cauchy's theorem for rectangles gives the independence of the
radius; for `Re a > 0` the circle contributes nothing as `δ → 0`.
-/

@[expose] public section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology Real Interval

noncomputable section

namespace Complex

/-- `e^z ≠ 1` for `0 < |z| < 2π`. -/
theorem exp_ne_one_of_norm_lt {z : ℂ} (h0 : z ≠ 0) (h : ‖z‖ < 2 * π) : cexp z ≠ 1 := by
  intro h'
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h'
  have hz : ‖z‖ = |(n : ℝ)| * (2 * π) := by
    rw [hn, norm_mul, norm_mul, norm_mul, norm_I, norm_intCast, Complex.norm_ofNat, norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    ring
  rcases eq_or_ne n 0 with rfl | hn0
  · exact h0 (by simpa using hn)
  · have : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
    nlinarith [Real.pi_pos]

/-- `|e^z - 1| ≥ |z|/2` for `|z| ≤ 1/2`. -/
theorem half_norm_le_norm_exp_sub_one {z : ℂ} (h : ‖z‖ ≤ 1 / 2) : ‖z‖ / 2 ≤ ‖cexp z - 1‖ := by
  have h1 := Complex.norm_exp_sub_one_sub_id_le (x := z) (by linarith)
  have h2 := norm_sub_le (cexp z - 1) (cexp z - 1 - z)
  rw [show cexp z - 1 - (cexp z - 1 - z) = z by ring] at h2
  nlinarith [norm_nonneg z]

/-- `(eᵗ)^a = e^{ta}` for real `t`. -/
private lemma ofReal_exp_cpow_eq (t : ℝ) (a : ℂ) :
    ((Real.exp t : ℝ) : ℂ) ^ a = cexp (t * a) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'), ← ofReal_log
    (Real.exp_pos t).le, Real.log_exp]

/-- `x ↦ x^a g(-x)` is continuous at every `0 < x < R`. -/
private lemma continuousAt_cpow_mul_comp_neg {g : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hg : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < R → DifferentiableAt ℂ g z) {x : ℝ} (hx : 0 < x)
    (hxR : x < R) :
    ContinuousAt (fun y : ℝ => (y : ℂ) ^ a * g (-y)) x := by
  have hn : ‖-(x : ℂ)‖ = x := by rw [norm_neg, norm_real, Real.norm_of_nonneg hx.le]
  refine (continuous_ofReal.continuousAt.cpow continuousAt_const
    (ofReal_mem_slitPlane.mpr hx)).mul ?_
  exact (hg _ (by rw [hn]; exact hx) (by rw [hn]; exact hxR)).continuousAt.comp
    continuous_ofReal.neg.continuousAt

/-- A horizontal side of the rectangle in the coordinate `w = log z`. -/
private lemma integral_horizontal {g : ℂ → ℂ} {a : ℂ} {R δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hδ₂ : 0 < δ₂) (h₁R : δ₁ < R) (h₂R : δ₂ < R)
    (hg : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < R → DifferentiableAt ℂ g z) {σ : ℝ}
    (hσ : cexp (σ * I) = -1) :
    ∫ x in (Real.log δ₁)..(Real.log δ₂), cexp ((a + 1) * (x + σ * I)) * g (cexp (x + σ * I)) =
      cexp ((a + 1) * (σ * I)) * ∫ x in δ₁..δ₂, (x : ℂ) ^ a * g (-x) := by
  have hcont : ContinuousOn (fun y : ℝ => (y : ℂ) ^ a * g (-y))
      (Real.exp '' uIcc (Real.log δ₁) (Real.log δ₂)) := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 : min (Real.log δ₁) (Real.log δ₂) ≤ u := hu.1
    have h2 : u ≤ max (Real.log δ₁) (Real.log δ₂) := hu.2
    have hle : Real.exp u ≤ max δ₁ δ₂ := by
      rcases le_total (Real.log δ₁) (Real.log δ₂) with h | h
      · rw [max_eq_right h] at h2
        exact (Real.exp_le_exp.mpr h2).trans (by rw [Real.exp_log hδ₂]; exact le_max_right _ _)
      · rw [max_eq_left h] at h2
        exact (Real.exp_le_exp.mpr h2).trans (by rw [Real.exp_log hδ₁]; exact le_max_left _ _)
    exact (continuousAt_cpow_mul_comp_neg hg (Real.exp_pos u)
      (hle.trans_lt (max_lt h₁R h₂R))).continuousWithinAt
  have h := intervalIntegral.integral_deriv_smul_comp' (f := Real.exp) (f' := Real.exp)
    (g := fun y : ℝ => (y : ℂ) ^ a * g (-y)) (a := Real.log δ₁) (b := Real.log δ₂)
    (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn hcont
  rw [Real.exp_log hδ₁, Real.exp_log hδ₂] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [Function.comp_apply, Complex.real_smul, ofReal_exp_cpow_eq]
  rw [exp_add, hσ, show cexp (x : ℂ) * -1 = -((Real.exp x : ℝ) : ℂ) by push_cast; ring,
    show (a + 1) * ((x : ℂ) + σ * I) = (a + 1) * (σ * I) + x * a + x by ring, exp_add, exp_add]
  push_cast
  ring

/-- A vertical side of the rectangle is a circle integral. -/
private lemma I_mul_vertical (g : ℂ → ℂ) (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) :
    I * (cexp ((a + 1) * ((Real.log δ : ℂ) + θ * I)) * g (cexp ((Real.log δ : ℂ) + θ * I))) =
      (δ : ℂ) ^ a * cexp (I * a * θ) * g (δ * cexp (I * θ)) * (I * δ * cexp (I * θ)) := by
  have hexp : cexp ((Real.log δ : ℂ) + θ * I) = δ * cexp (I * θ) := by
    rw [exp_add, ← ofReal_exp, Real.exp_log hδ, mul_comm (θ : ℂ)]
  have hpow : (δ : ℂ) ^ a = cexp (Real.log δ * a) := by
    rw [cpow_def_of_ne_zero (by exact_mod_cast hδ.ne'), ← ofReal_log hδ.le]
  have hδe : (δ : ℂ) = cexp (Real.log δ) := by rw [← ofReal_exp, Real.exp_log hδ]
  rw [hexp, hpow]
  generalize g (δ * cexp (I * θ)) = c
  rw [hδe]
  rw [show (a + 1) * ((Real.log δ : ℂ) + θ * I) = Real.log δ * a + I * a * θ + Real.log δ +
    I * θ by ring, exp_add, exp_add, exp_add]
  ring

/-- **Independence of the radius**: for `g` holomorphic on `0 < |z| < R` and `0 < δ₁ ≤ δ₂ < R`,
the circle parts of the keyhole integrals of radii `δ₂` and `δ₁` differ by
`(e^{-iπa} - e^{iπa}) ∫_{δ₁}^{δ₂} x^a g(-x) dx`. -/
theorem keyholeCircleIntegral_sub {g : ℂ → ℂ} {a : ℂ} {R δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁)
    (h₁₂ : δ₁ ≤ δ₂) (h₂R : δ₂ < R)
    (hg : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < R → DifferentiableAt ℂ g z) :
    (∫ θ in (-π)..π, (δ₂ : ℂ) ^ a * cexp (I * a * θ) * g (δ₂ * cexp (I * θ)) *
        (I * δ₂ * cexp (I * θ))) -
      ∫ θ in (-π)..π, (δ₁ : ℂ) ^ a * cexp (I * a * θ) * g (δ₁ * cexp (I * θ)) *
        (I * δ₁ * cexp (I * θ)) =
      (cexp (-(π * I * a)) - cexp (π * I * a)) * ∫ x in δ₁..δ₂, (x : ℂ) ^ a * g (-x) := by
  have hδ₂ : 0 < δ₂ := hδ₁.trans_le h₁₂
  have h₁R : δ₁ < R := h₁₂.trans_lt h₂R
  set G : ℂ → ℂ := fun w => cexp ((a + 1) * w) * g (cexp w)
  have hrect := integral_boundary_rect_eq_zero_of_differentiableOn G
    ((Real.log δ₁ : ℂ) + ((-π : ℝ) : ℂ) * I) ((Real.log δ₂ : ℂ) + ((π : ℝ) : ℂ) * I)
    (fun w hw => by
      rw [mem_reProdIm] at hw
      have h1 := hw.1
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one,
        sub_zero, add_zero] at h1
      rw [uIcc_of_le (Real.log_le_log hδ₁ h₁₂)] at h1
      have hn : ‖cexp w‖ = Real.exp w.re := norm_exp w
      have hlo : δ₁ ≤ Real.exp w.re := by
        rw [← Real.exp_log hδ₁]; exact Real.exp_le_exp.mpr h1.1
      have hhi : Real.exp w.re ≤ δ₂ := by
        rw [← Real.exp_log hδ₂]; exact Real.exp_le_exp.mpr h1.2
      have hgw := hg (cexp w) (by rw [hn]; linarith) (by rw [hn]; linarith)
      exact (((differentiableAt_const _).mul differentiableAt_id).cexp.mul
        (hgw.comp w differentiableAt_exp)).differentiableWithinAt)
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero,
    add_zero, add_im, mul_im, zero_add, smul_eq_mul] at hrect
  have hm : cexp (((-π : ℝ) : ℂ) * I) = -1 := by
    rw [ofReal_neg, neg_mul, exp_neg, exp_pi_mul_I]; norm_num
  have hp : cexp (((π : ℝ) : ℂ) * I) = -1 := exp_pi_mul_I
  have hbot := integral_horizontal (a := a) hδ₁ hδ₂ h₁R h₂R hg hm
  have htop := integral_horizontal (a := a) hδ₁ hδ₂ h₁R h₂R hg hp
  simp only [G] at hrect
  rw [hbot, htop] at hrect
  have hvert : ∀ δ : ℝ, 0 < δ → I * ∫ θ in (-π)..π, G ((Real.log δ : ℂ) + θ * I) =
      ∫ θ in (-π)..π, (δ : ℂ) ^ a * cexp (I * a * θ) * g (δ * cexp (I * θ)) *
        (I * δ * cexp (I * θ)) := fun δ hδ => by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ => I_mul_vertical g a hδ θ
  simp only [G] at hvert
  push_cast at hrect
  rw [hvert δ₂ hδ₂, hvert δ₁ hδ₁] at hrect
  have e1 : cexp ((a + 1) * (-(π : ℂ) * I)) = -cexp (-(π * I * a)) := by
    rw [show (a + 1) * (-(π : ℂ) * I) = -(π * I * a) + -(π * I) by ring, exp_add, exp_neg
      (π * I), exp_pi_mul_I]
    ring
  have e2 : cexp ((a + 1) * ((π : ℂ) * I)) = -cexp (π * I * a) := by
    rw [show (a + 1) * ((π : ℂ) * I) = π * I * a + π * I by ring, exp_add, exp_pi_mul_I]
    ring
  rw [e1, e2] at hrect
  linear_combination hrect

/-- **Keyhole integral for `Re a > 0`**: for `g` holomorphic on `0 < |z| < R` with
`g(z) = O(1/z)` at `0`, `Re a > 0`, `x^a g(-x)` integrable on `(0, ∞)` and `0 < δ < R`, the
keyhole integral of `z^a g(z)` of radius `δ` is `(e^{-iπa} - e^{iπa}) ∫_0^∞ x^a g(-x) dx`. -/
theorem keyholeIntegral_eq_mul_integral_Ioi {g : ℂ → ℂ} {a : ℂ} {R δ : ℝ} (ha : 0 < a.re)
    (hδ : 0 < δ) (hδR : δ < R) (hg : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < R → DifferentiableAt ℂ g z)
    (hint : IntegrableOn (fun x : ℝ => (x : ℂ) ^ a * g (-x)) (Ioi 0))
    (hbd : ∃ M r : ℝ, 0 < r ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r → ‖z * g z‖ ≤ M) :
    (cexp (-(π * I * a)) - cexp (π * I * a)) * (∫ x in Ioi δ, (x : ℂ) ^ a * g (-x)) +
      ∫ θ in (-π)..π, (δ : ℂ) ^ a * cexp (I * a * θ) * g (δ * cexp (I * θ)) *
        (I * δ * cexp (I * θ)) =
      (cexp (-(π * I * a)) - cexp (π * I * a)) * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ a * g (-x) := by
  set f : ℝ → ℂ := fun x => (x : ℂ) ^ a * g (-x)
  set A : ℂ := cexp (-(π * I * a)) - cexp (π * I * a)
  set C : ℝ → ℂ := fun d => ∫ θ in (-π)..π, (d : ℂ) ^ a * cexp (I * a * θ) *
    g (d * cexp (I * θ)) * (I * d * cexp (I * θ))
  change A * (∫ x in Ioi δ, f x) + C δ = A * ∫ x in Ioi 0, f x
  have hK : ∀ d, 0 < d → d ≤ δ → A * (∫ x in Ioi d, f x) + C d = A * (∫ x in Ioi δ, f x) + C δ :=
    fun d hd hle => by
      have h1 := keyholeCircleIntegral_sub (a := a) hd hle hδR hg
      have h2 := integral_Ioi_sub_Ioi (hint.mono_set (Ioi_subset_Ioi hd.le)) hle
      simp only [C, A, f] at h1 h2 ⊢
      linear_combination A * h2 - h1
  have hE : Tendsto (fun d => ∫ x in Ioi d, f x) (𝓝[>] 0) (𝓝 (∫ x in Ioi 0, f x)) := by
    have hII : IntervalIntegrable f volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
        (hint.mono_set Ioc_subset_Ioi_self)
    have hP := (intervalIntegral.continuousOn_primitive_interval' hII
      (left_mem_uIcc (a := (0 : ℝ)) (b := 1))) 0 left_mem_uIcc
    have hP' : Tendsto (fun d => ∫ x in (0 : ℝ)..d, f x) (𝓝[>] 0) (𝓝 0) := by
      have hmem : [[(0 : ℝ), 1]] ∈ 𝓝[>] (0 : ℝ) := by
        rw [uIcc_of_le zero_le_one]
        exact mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) Ioo_subset_Icc_self
      simpa using hP.tendsto.mono_left (nhdsWithin_le_of_mem hmem)
    have := hP'.const_sub (∫ x in Ioi 0, f x)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with d hd
    rw [← integral_interval_add_Ioi hint (hint.mono_set (Ioi_subset_Ioi (le_of_lt hd)))]
    ring
  have hC : Tendsto C (𝓝[>] 0) (𝓝 0) := by
    obtain ⟨M, r, hr, hM⟩ := hbd
    have hb : Tendsto (fun d : ℝ => d ^ a.re * Real.exp (π * |a.im|) * M * |π - -π|)
        (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun d : ℝ => d ^ a.re) (𝓝 0) (𝓝 0) := by
        have := (Real.continuousAt_rpow_const 0 a.re (Or.inr ha.le)).tendsto
        rwa [Real.zero_rpow ha.ne'] at this
      simpa using ((h0.mul_const (Real.exp (π * |a.im|))).mul_const M).mul_const
        |π - -π| |>.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [Ioo_mem_nhdsGT hr] with d hd
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_
    have hθ' : |θ| ≤ π := by
      rw [uIoc_of_le (by linarith [Real.pi_pos])] at hθ
      exact abs_le.mpr ⟨hθ.1.le, hθ.2⟩
    set z : ℂ := d * cexp (I * θ)
    have hz : ‖z‖ = d := by
      rw [norm_mul, norm_real, Real.norm_of_nonneg hd.1.le, mul_comm I, norm_exp_ofReal_mul_I,
        mul_one]
    have he : ‖cexp (I * a * θ)‖ ≤ Real.exp (π * |a.im|) := by
      rw [norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have : (I * a * θ).re = -(a.im * θ) := by simp
      rw [this]
      calc -(a.im * θ) ≤ |a.im * θ| := neg_le_abs _
        _ = |a.im| * |θ| := abs_mul _ _
        _ ≤ |a.im| * π := by gcongr
        _ = π * |a.im| := mul_comm _ _
    have hzg := hM z (by rw [hz]; exact hd.1) (by rw [hz]; exact hd.2)
    calc ‖(d : ℂ) ^ a * cexp (I * a * θ) * g z * (I * d * cexp (I * θ))‖
        = d ^ a.re * ‖cexp (I * a * θ)‖ * ‖z * g z‖ := by
          rw [show (d : ℂ) ^ a * cexp (I * a * θ) * g z * (I * d * cexp (I * θ)) =
            I * ((d : ℂ) ^ a * cexp (I * a * θ) * (z * g z)) by simp only [z]; ring,
            norm_mul, norm_I, one_mul, norm_mul, norm_mul,
            norm_cpow_eq_rpow_re_of_pos hd.1]
      _ ≤ d ^ a.re * Real.exp (π * |a.im|) * M := by
          have := Real.rpow_nonneg hd.1.le a.re
          gcongr
  have hlim := (hE.const_mul A).add hC
  rw [add_zero] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [Ioo_mem_nhdsGT hδ] with d hd
  exact (hK d hd.1 hd.2.le).symm

/-- `t^u ≤ δ^{-N} + t^N` for `0 < δ ≤ t` and `|u| ≤ N`. -/
private lemma rpow_le_rpow_neg_add_pow {δ t u : ℝ} {N : ℕ} (hδ : 0 < δ) (ht : δ ≤ t)
    (hu : |u| ≤ N) : t ^ u ≤ δ ^ (-(N : ℝ)) + t ^ (N : ℝ) := by
  have ht0 : 0 < t := hδ.trans_le ht
  have h1 := Real.rpow_nonneg hδ.le (-(N : ℝ))
  have h2 := Real.rpow_nonneg ht0.le (N : ℝ)
  rcases le_or_gt t 1 with ht1 | ht1
  · have := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (show -(N : ℝ) ≤ u by
      linarith [neg_abs_le u])
    have := Real.rpow_le_rpow_of_nonpos hδ ht (show -(N : ℝ) ≤ 0 by
      linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le ht1.le (show u ≤ (N : ℝ) by
      linarith [le_abs_self u])
    linarith

/-- **The keyhole integral is entire in the exponent**: for `g` continuous on the circle
`|z| = δ` and on `(-∞, -δ]`, with `|g(-x)| ≤ K e^{-bx}` for `x ≥ δ` (`b > 0`), the keyhole
integral of `z^a g(z)` of radius `δ` is an entire function of `a`. -/
theorem differentiable_keyholeIntegral {g : ℂ → ℂ} {δ b K : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    (hcirc : ContinuousOn g (Metric.sphere 0 δ))
    (hedge : ContinuousOn (fun x : ℝ => g (-x)) (Ioi δ))
    (hdec : ∀ x : ℝ, δ < x → ‖g (-x)‖ ≤ K * Real.exp (-b * x)) :
    Differentiable ℂ (fun a : ℂ => (cexp (-(π * I * a)) - cexp (π * I * a)) *
      (∫ x in Ioi δ, (x : ℂ) ^ a * g (-x)) +
        ∫ θ in (-π)..π, (δ : ℂ) ^ a * cexp (I * a * θ) * g (δ * cexp (I * θ)) *
          (I * δ * cexp (I * θ))) := by
  have hpre : Differentiable ℂ (fun a : ℂ => cexp (-(π * I * a)) - cexp (π * I * a)) := by
    fun_prop
  -- the edges
  have hE : Differentiable ℂ (fun a : ℂ => ∫ x in Ioi δ, (x : ℂ) ^ a * g (-x)) := by
    rw [← differentiableOn_univ]
    refine differentiableOn_integral_Ioi_of_locally_dominated isOpen_univ δ
      (fun a _ => ?_) ?_ (fun a₀ _ => ?_)
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      have hx0 : 0 < x := hδ.trans hx
      exact ((continuous_ofReal.continuousAt.cpow continuousAt_const
        (ofReal_mem_slitPlane.mpr hx0)).continuousWithinAt).mul (hedge x hx)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (hδ.trans hx).ne'
      exact (fun a _ => ((differentiableAt_id.const_cpow (Or.inl hx0)).mul_const
        _).differentiableWithinAt)
    · set N : ℕ := ⌈|a₀.re|⌉₊ + 1
      refine ⟨Metric.ball a₀ 1, Metric.ball_mem_nhds _ one_pos, fun x =>
        (δ ^ (-(N : ℝ)) + x ^ (N : ℝ)) * (K * Real.exp (-b * x)), ?_, ?_⟩
      · have h1 := (exp_neg_integrableOn_Ioi δ hb).const_mul (δ ^ (-(N : ℝ)) * K)
        have h2 := ((integrableOn_rpow_mul_exp_neg_mul_rpow (s := (N : ℝ)) (p := 1)
          (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]) one_pos hb).mono_set
          (Ioi_subset_Ioi hδ.le)).const_mul K
        refine IntegrableOn.congr_fun (Integrable.add h1 h2) (fun x hx => ?_) measurableSet_Ioi
        simp only [Pi.add_apply, Real.rpow_one]
        ring
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx a ha
        have hx0 : 0 < x := hδ.trans hx
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : |a.re| ≤ N := by
          have h1 : ‖a - a₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at ha
          have h2 := abs_re_le_norm (a - a₀)
          have h3 := Nat.le_ceil |a₀.re|
          simp only [sub_re] at h2
          push_cast [N]
          have := abs_sub_abs_le_abs_sub a.re a₀.re
          linarith
        exact mul_le_mul (rpow_le_rpow_neg_add_pow hδ hx.le hre) (hdec x hx) (norm_nonneg _)
          (by positivity)
  -- the circle
  have hC : Differentiable ℂ (fun a : ℂ => ∫ θ in (-π)..π, (δ : ℂ) ^ a * cexp (I * a * θ) *
      g (δ * cexp (I * θ)) * (I * δ * cexp (I * θ))) := by
    have hδ0 : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
    have hgc : Continuous (fun θ : ℝ => g (δ * cexp (I * θ))) := by
      refine hcirc.comp_continuous (by fun_prop) fun θ => ?_
      rw [mem_sphere_zero_iff_norm, norm_mul, norm_real, Real.norm_of_nonneg hδ.le, mul_comm I,
        norm_exp_ofReal_mul_I, mul_one]
    obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) δ).exists_bound_of_continuousOn hcirc
    rw [← differentiableOn_univ]
    refine differentiableOn_intervalIntegral_of_locally_dominated isOpen_univ (-π) π
      (fun a _ => ?_) ?_ (fun a₀ _ => ?_)
    · exact Continuous.aestronglyMeasurable
        (((continuous_const.mul (by fun_prop)).mul hgc).mul (by fun_prop))
    · exact Eventually.of_forall fun θ a _ => (((differentiableAt_id.const_cpow
        (Or.inl hδ0)).mul (by fun_prop)).mul_const _).mul_const _ |>.differentiableWithinAt
    · set N : ℕ := ⌈|a₀.re|⌉₊ + 1
      refine ⟨Metric.ball a₀ 1, Metric.ball_mem_nhds _ one_pos, fun _ =>
        (δ ^ (-(N : ℝ)) + δ ^ (N : ℝ)) * Real.exp (π * (|a₀.im| + 1)) * M * δ, ?_, ?_⟩
      · rw [uIoc_of_le (by linarith [Real.pi_pos])]
        exact integrableOn_const (by simp)
      · filter_upwards [ae_restrict_mem measurableSet_uIoc] with θ hθ a ha
        have hθ' : |θ| ≤ π := by
          rw [uIoc_of_le (by linarith [Real.pi_pos])] at hθ
          exact abs_le.mpr ⟨hθ.1.le, hθ.2⟩
        have h1 : ‖a - a₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at ha
        have hre : |a.re| ≤ N := by
          have h2 := abs_re_le_norm (a - a₀)
          have h3 := Nat.le_ceil |a₀.re|
          simp only [sub_re] at h2
          push_cast [N]
          have := abs_sub_abs_le_abs_sub a.re a₀.re
          linarith
        have him : |a.im| ≤ |a₀.im| + 1 := by
          have h2 := abs_im_le_norm (a - a₀)
          simp only [sub_im] at h2
          have := abs_sub_abs_le_abs_sub a.im a₀.im
          linarith
        have hz : δ * cexp (I * θ) ∈ Metric.sphere (0 : ℂ) δ := by
          rw [mem_sphere_zero_iff_norm, norm_mul, norm_real, Real.norm_of_nonneg hδ.le,
            mul_comm I, norm_exp_ofReal_mul_I, mul_one]
        have he : ‖cexp (I * a * θ)‖ ≤ Real.exp (π * (|a₀.im| + 1)) := by
          rw [norm_exp]
          refine Real.exp_le_exp.mpr ?_
          have : (I * a * θ).re = -(a.im * θ) := by simp
          rw [this]
          calc -(a.im * θ) ≤ |a.im * θ| := neg_le_abs _
            _ = |a.im| * |θ| := abs_mul _ _
            _ ≤ (|a₀.im| + 1) * π := by gcongr
            _ = π * (|a₀.im| + 1) := mul_comm _ _
        have hI : ‖I * δ * cexp (I * θ)‖ = δ := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_real, Real.norm_of_nonneg hδ.le,
            mul_comm I, norm_exp_ofReal_mul_I, mul_one]
        rw [norm_mul, norm_mul, norm_mul, hI, norm_cpow_eq_rpow_re_of_pos hδ]
        have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ hz)
        have := rpow_le_rpow_neg_add_pow hδ le_rfl hre
        gcongr
        exact hM _ hz
  exact (hpre.mul hE).add hC

end Complex
