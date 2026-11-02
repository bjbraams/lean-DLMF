/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Coalescing critical points (DLMF §§2.3(v), 2.4(v))

Bleistein's method for an endpoint and a stationary point that coalesce, and the cubic change
of variable of Chester, Friedman and Ursell.

## Main results

* `bleistein_quadratic`: `p(α,t) = ½w² - aw + b` (DLMF 2.3.25) with `a = bleisteinA p α`,
  `b = bleisteinB p α` (2.3.26) and `w = bleisteinW p α t` (2.3.27).
* `bleisteinW_zero`, `bleisteinW_self`: `t = 0` corresponds to `w = 0` and `t = α` to `w = a`.
* `bleisteinW_hasDerivAt`, `bleisteinW_hasDerivAt_self`, `bleisteinW_hasDerivAt_self'`: the
  derivative 2.3.28 and regularity of `t ↦ w`.
* `bleistein_transform`, `bleistein_transform'`: the transformation 2.3.24, 2.3.29–2.3.30.
* `bleistein_uniform`: Bleistein's uniform expansion (DLMF 2.3.31–2.3.33).
* `cfu_deriv`, `cfu_airy_form`: the cubic change of variable 2.4.18–2.4.20 and the reduction
  2.4.21 to Airy form.

## Implementation notes

Bleistein's method concerns `I(α, x) = ∫₀ᵏ e^{-xp(α,t)} q(α,t) t^{λ-1} dt` (2.3.24), where the
minimum of `p(α, ·)` on `[0, k)` is at `t = α`. The expansion 2.3.32 is uniform in `α`, with
remainder bounded by the comparison integral `∫₀^∞ exp(-½τ² + yτ) |τ - y|ᴺ τ^{λ-1} dτ` at
`y = a√x` (DLMF obtains 2.3.32 "formally"; the remainder form is the one produced by
term-by-term integration with a uniform Taylor remainder for `f(α, w)` about `w = a`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset
open scoped Topology

namespace DLMF.AsymptoticApproximations

section Bleistein

variable {p : ℝ → ℝ → ℝ} {α t : ℝ}

/-- DLMF 2.3.25: with `a`, `b`, `w` from 2.3.26–2.3.27, `p(α, t) = ½w² - aw + b`, provided the
minimum of `p(α, ·)` is at `t = α` (`p(α,α) ≤ p(α,0)` and `p(α,α) ≤ p(α,t)`). -/
@[dlmf 2.3.E25]
theorem bleistein_quadratic (h0 : p α α ≤ p α 0) (ht : p α α ≤ p α t) :
    p α t = bleisteinW p α t ^ 2 / 2 - bleisteinA p α * bleisteinW p α t + bleisteinB p α := by
  have hA : bleisteinA p α ^ 2 = 2 * p α 0 - 2 * p α α := by
    unfold bleisteinA
    split_ifs <;> simp [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * p α 0 - 2 * p α α)]
  have hS := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * p α t - 2 * p α α)
  unfold bleisteinW bleisteinB
  split_ifs <;> nlinarith [hA, hS]

/-- DLMF §2.3(v), before 2.3.26: `t = 0` corresponds to `w = 0`. -/
@[dlmf 2.3.E26, dlmf 2.3.v]
theorem bleisteinW_zero : bleisteinW p α 0 = 0 := by
  unfold bleisteinW bleisteinA
  by_cases h1 : α ≤ 0 <;> by_cases h2 : 0 ≤ α <;> simp only [h1, h2, ↓reduceIte]
  · have : α = 0 := le_antisymm h1 h2
    subst this; simp
  · ring
  · ring
  · exact absurd (le_of_lt (not_le.1 h1)) h2

/-- DLMF §2.3(v), before 2.3.26: the stationary point `t = α` corresponds to `w = a`. -/
@[dlmf 2.3.E26, dlmf 2.3.v]
theorem bleisteinW_self : bleisteinW p α α = bleisteinA p α := by
  simp [bleisteinW]

/-- DLMF 2.3.28: for `t ≠ α` with `p(α, t) > p(α, α)` and `p(α, ·)` differentiable at `t`,
`dw/dt = ± (2p(α,t) - 2p(α,α))^{-1/2} ∂p(α,t)/∂t`, upper sign for `t > α`. -/
@[dlmf 2.3.E28]
theorem bleisteinW_hasDerivAt {p' : ℝ} (hd : HasDerivAt (p α) p' t) (hpt : p α α < p α t)
    (hne : t ≠ α) :
    HasDerivAt (bleisteinW p α) ((if α < t then 1 else -1) * p' /
      Real.sqrt (2 * p α t - 2 * p α α)) t := by
  have hpos : 0 < 2 * p α t - 2 * p α α := by linarith
  have hg : HasDerivAt (fun s => 2 * p α s - 2 * p α α) (2 * p') t := by
    simpa using (hd.const_mul 2).sub_const (2 * p α α)
  have hsq := hg.sqrt hpos.ne'
  have hS : Real.sqrt (2 * p α t - 2 * p α α) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  rcases lt_or_gt_of_ne hne with h | h
  · -- `t < α`: lower sign
    have hev : bleisteinW p α =ᶠ[𝓝 t] fun s => bleisteinA p α -
        Real.sqrt (2 * p α s - 2 * p α α) := by
      filter_upwards [Iio_mem_nhds h] with s hs
      simp [bleisteinW, not_le.mpr (show s < α from hs)]
    refine ((hsq.const_sub (bleisteinA p α)).congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [show ¬ (α < t) from not_lt.mpr h.le, ↓reduceIte]
    field_simp
  · have hev : bleisteinW p α =ᶠ[𝓝 t] fun s => bleisteinA p α +
        Real.sqrt (2 * p α s - 2 * p α α) := by
      filter_upwards [Ioi_mem_nhds h] with s hs
      simp [bleisteinW, le_of_lt (show α < s from hs)]
    refine ((hsq.const_add (bleisteinA p α)).congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [h, ↓reduceIte]
    field_simp

/-- DLMF §2.3(v), after 2.3.28: the map `t ↦ w` is free from singularity at `t = α`: if
`p(α, ·)` is twice differentiable near `α` with `∂p/∂t(α,α) = 0` and `∂²p/∂t²(α,α) > 0`, and the
minimum of `p(α, ·)` is at `α`, then `w` is differentiable at `t = α` with
`dw/dt = (∂²p/∂t²(α,α))^{1/2}`. This is stronger than DLMF, which assumes `∂²p/∂t²(α,α) > 0`. -/
@[dlmf 2.3.v]
theorem bleisteinW_hasDerivAt_self' {p₂ : ℝ} (hp : ContDiffAt ℝ 2 (p α) α)
    (hd1 : deriv (p α) α = 0) (hd2 : deriv (deriv (p α)) α = p₂)
    (hmin : ∀ s, p α α ≤ p α s) :
    HasDerivAt (bleisteinW p α) (Real.sqrt p₂) α := by
  set P := p α with hP
  have hev : ∀ᶠ y in 𝓝 α, DifferentiableAt ℝ P y :=
    (hp.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hdd : DifferentiableAt ℝ (deriv P) α := by
    have h1 : DifferentiableAt ℝ (fderiv ℝ P) α :=
      (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have : deriv P = fun x => fderiv ℝ P x 1 := by funext x; rfl
    rw [this]; exact h1.clm_apply (differentiableAt_const _)
  have hP2 : HasDerivAt (deriv P) p₂ α := hd2 ▸ hdd.hasDerivAt
  -- L'Hôpital: 2(P t - P α)/(t-α)² → p₂
  have hlim : Tendsto (fun t => (2 * P t - 2 * P α) / (t - α) ^ 2) (𝓝[≠] α) (𝓝 p₂) := by
    have hev' : ∀ᶠ y in 𝓝[≠] α, DifferentiableAt ℝ P y := nhdsWithin_le_nhds hev
    refine HasDerivAt.lhopital_zero_nhdsNE (f' := fun t => 2 * deriv P t)
      (g' := fun t => 2 * (t - α))
      (hev'.mono fun y hy => by simpa using (hy.hasDerivAt.const_mul 2).sub_const (2 * P α))
      (Eventually.of_forall fun y => by
        simpa using ((hasDerivAt_id y).sub_const α).fun_pow 2)
      (eventually_nhdsWithin_of_forall fun y hy => by
        have : y - α ≠ 0 := sub_ne_zero.mpr hy
        positivity) ?_ ?_ ?_
    · have hc : ContinuousAt (fun t => 2 * P t - 2 * P α) α :=
        (hp.continuousAt.const_mul 2).sub continuousAt_const
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · have hc : ContinuousAt (fun t : ℝ => (t - α) ^ 2) α := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · have hs := hP2.tendsto_slope
      refine hs.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
      have : y - α ≠ 0 := sub_ne_zero.mpr hy
      simp only [slope_def_field, hd1, sub_zero]
      field_simp
  rw [hasDerivAt_iff_tendsto_slope]
  refine ((Real.continuous_sqrt.tendsto p₂).comp hlim).congr'
    (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have hne : y - α ≠ 0 := sub_ne_zero.mpr hy
  have h0 : 0 ≤ 2 * P y - 2 * P α := by linarith [hmin y]
  simp only [Function.comp, slope_def_field, bleisteinW_self]
  rw [Real.sqrt_div h0, Real.sqrt_sq_eq_abs]
  unfold bleisteinW
  rcases lt_or_gt_of_ne hy with h | h
  · simp only [not_le.mpr h, ↓reduceIte]
    rw [abs_of_neg (sub_neg.mpr h)]
    field_simp
    ring
  · simp only [h.le, ↓reduceIte]
    rw [abs_of_pos (sub_pos.mpr h)]
    field_simp
    ring

/-- DLMF §2.3(v), after 2.3.28: the map `t ↦ w` is free from singularity at `t = α`: if
`p(α, ·)` is twice differentiable near `α` with `∂p/∂t(α,α) = 0` and `∂²p/∂t²(α,α) > 0`, and the
minimum of `p(α, ·)` is at `α`, then `w` is differentiable at `t = α` with
`dw/dt = (∂²p/∂t²(α,α))^{1/2}`. -/
@[dlmf 2.3.v]
theorem bleisteinW_hasDerivAt_self {p₂ : ℝ} (hp : ContDiffAt ℝ 2 (p α) α)
    (hd1 : deriv (p α) α = 0) (hd2 : deriv (deriv (p α)) α = p₂) (_hp₂ : 0 < p₂)
    (hmin : ∀ s, p α α ≤ p α s) :
    HasDerivAt (bleisteinW p α) (Real.sqrt p₂) α :=
  bleisteinW_hasDerivAt_self' hp hd1 hd2 hmin

/-- DLMF 2.3.24, 2.3.29–2.3.30: for finite `k`, if `t ↦ w = W(t)` maps `[0, k]` onto `[0, κ]`
with inverse `T` (`W(T(w)) = w`) of class `C¹`, `T(0) = 0`, `T(κ) = k`, `T' > 0`, and
`p(α, T(w)) = ½w² - aw + b`, then
`I(α,x) = ∫₀ᵏ e^{-xp(α,t)} q(α,t) t^{λ-1} dt
= e^{-xp(α,0)} ∫₀^κ exp(-x(½w² - aw)) f(α,w) w^{λ-1} dw`,
`f(α, w) = q(α, t)(t/w)^{λ-1} dt/dw` (2.3.30), for `λ > 0` and `q(α, ·)` continuous. This is
stronger than DLMF, which assumes `λ > 0` and the continuity of `q(α, ·)`. -/
@[dlmf 2.3.E24, dlmf 2.3.E29, dlmf 2.3.E30]
theorem bleistein_transform' {q : ℝ → ℝ → ℝ} {T : ℝ → ℝ} {k κ lam a b x : ℝ} (hk : 0 < k)
    (hκ : 0 < κ) (hT : ContDiffOn ℝ 1 T (Icc 0 κ)) (hT0 : T 0 = 0) (hTκ : T κ = k)
    (hT' : ∀ w ∈ Icc 0 κ, 0 < derivWithin T (Icc 0 κ) w)
    (hpT : ∀ w ∈ Icc 0 κ, p α (T w) = w ^ 2 / 2 - a * w + b) (hb : b = p α 0) :
    ∫ t in (0 : ℝ)..k, Real.exp (-x * p α t) * q α t * t ^ (lam - 1) =
      Real.exp (-x * p α 0) * ∫ w in (0 : ℝ)..κ, Real.exp (-x * (w ^ 2 / 2 - a * w)) *
        (q α (T w) * (T w / w) ^ (lam - 1) * derivWithin T (Icc 0 κ) w) * w ^ (lam - 1) := by
  set T' := derivWithin T (Icc 0 κ) with hT'def
  have hdiff : DifferentiableOn ℝ T (Icc 0 κ) := hT.differentiableOn one_ne_zero
  have hcont : ContinuousOn T (Icc 0 κ) := hdiff.continuousOn
  have hder : ∀ w ∈ Icc 0 κ, HasDerivWithinAt T (T' w) (Icc 0 κ) w :=
    fun w hw => (hdiff w hw).hasDerivWithinAt
  have hmono : StrictMonoOn T (Icc 0 κ) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 κ) hcont fun w hw => ?_
    rw [interior_Icc] at hw
    have := hT' w (Ioo_subset_Icc_self hw)
    rwa [hT'def, derivWithin_of_mem_nhds (Icc_mem_nhds hw.1 hw.2)] at this
  have himage : T '' Icc 0 κ = Icc 0 k := by
    rw [hcont.image_Icc_of_monotoneOn hκ.le hmono.monotoneOn, hT0, hTκ]
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hder
    hmono.injOn (fun t => Real.exp (-x * p α t) * q α t * t ^ (lam - 1))
  rw [himage] at hchange
  rw [intervalIntegral.integral_of_le hk.le, ← integral_Icc_eq_integral_Ioc, hchange,
    intervalIntegral.integral_of_le hκ.le, integral_Icc_eq_integral_Ioc, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun w hw => ?_
  have hwI : w ∈ Icc 0 κ := Ioc_subset_Icc_self hw
  have hw0 : 0 < w := hw.1
  have hTw : 0 ≤ T w := by
    rw [← hT0]; exact hmono.monotoneOn (left_mem_Icc.mpr hκ.le) hwI hw0.le
  simp only [smul_eq_mul]
  rw [abs_of_pos (hT' w hwI), hpT w hwI, ← hb, Real.div_rpow hTw hw0.le]
  have hwr : w ^ (lam - 1) ≠ 0 := (Real.rpow_pos_of_pos hw0 _).ne'
  have he : Real.exp (-x * (w ^ 2 / 2 - a * w + b)) =
      Real.exp (-x * b) * Real.exp (-x * (w ^ 2 / 2 - a * w)) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  field_simp

/-- DLMF 2.3.24, 2.3.29–2.3.30: for finite `k`, if `t ↦ w = W(t)` maps `[0, k]` onto `[0, κ]`
with inverse `T` (`W(T(w)) = w`) of class `C¹`, `T(0) = 0`, `T(κ) = k`, `T' > 0`, and
`p(α, T(w)) = ½w² - aw + b`, then
`I(α,x) = ∫₀ᵏ e^{-xp(α,t)} q(α,t) t^{λ-1} dt
= e^{-xp(α,0)} ∫₀^κ exp(-x(½w² - aw)) f(α,w) w^{λ-1} dw`,
`f(α, w) = q(α, t)(t/w)^{λ-1} dt/dw` (2.3.30), for `λ > 0` and `q(α, ·)` continuous. -/
@[dlmf 2.3.E24, dlmf 2.3.E29, dlmf 2.3.E30]
theorem bleistein_transform {q : ℝ → ℝ → ℝ} {T : ℝ → ℝ} {k κ lam a b x : ℝ} (hk : 0 < k)
    (hκ : 0 < κ) (_hlam : 0 < lam) (_hq : ContinuousOn (q α) (Icc 0 k))
    (hT : ContDiffOn ℝ 1 T (Icc 0 κ)) (hT0 : T 0 = 0) (hTκ : T κ = k)
    (hT' : ∀ w ∈ Icc 0 κ, 0 < derivWithin T (Icc 0 κ) w)
    (hpT : ∀ w ∈ Icc 0 κ, p α (T w) = w ^ 2 / 2 - a * w + b) (hb : b = p α 0) :
    ∫ t in (0 : ℝ)..k, Real.exp (-x * p α t) * q α t * t ^ (lam - 1) =
      Real.exp (-x * p α 0) * ∫ w in (0 : ℝ)..κ, Real.exp (-x * (w ^ 2 / 2 - a * w)) *
        (q α (T w) * (T w / w) ^ (lam - 1) * derivWithin T (Icc 0 κ) w) * w ^ (lam - 1) :=
  bleistein_transform' hk hκ hT hT0 hTκ hT' hpT hb

/-- DLMF 2.3.31–2.3.33 (**Bleistein's uniform expansion**): let `λ > 0`, `κ > 0`, and for `α` in
`[α₁, α₂]` let `a(α) ≤ a₂ < κ`. Suppose that `f(α, w)` (measurable in `w`) has the expansion
`f(α,w) = ∑ φₛ(α)(w - a)ˢ` (2.3.31) in the uniform sense that for each `N` there is `C` with
`|f(α,w) - ∑_{s<N} φₛ(α)(w-a)ˢ| ≤ C|w - a|ᴺ` for all `α ∈ [α₁, α₂]`, `w ∈ [0, κ]`. Then, uniformly
for `α ∈ [α₁, α₂]`, the integral 2.3.29,
`J(α,x) = e^{-xb} ∫₀^κ exp(-x(½w² - aw)) f(α,w) w^{λ-1} dw`, satisfies (2.3.32)
`J(α,x) = e^{-xb} x^{-λ/2} (∑_{s<N} φₛ(α) Fₛ(a√x) x^{-s/2} + O(x^{-N/2} G_N(a√x)))`, with
`Fₛ = bleisteinF λ s` (2.3.33) and `G_N(y) = ∫₀^∞ exp(-½τ² + yτ) |τ - y|ᴺ τ^{λ-1} dτ`. -/
@[dlmf 2.3.E31, dlmf 2.3.E32, dlmf 2.3.E33]
theorem bleistein_uniform {f : ℝ → ℝ → ℝ} {φ : ℕ → ℝ → ℝ} {aα bα : ℝ → ℝ}
    {lam κ α₁ α₂ a₂ : ℝ} (hlam : 0 < lam) (hκ : 0 < κ) (ha₂ : a₂ < κ)
    (ha : ∀ α ∈ Icc α₁ α₂, aα α ≤ a₂)
    (hfm : ∀ α ∈ Icc α₁ α₂, AEStronglyMeasurable (f α) (volume.restrict (Ioc 0 κ)))
    (hT : ∀ N : ℕ, ∃ C, ∀ α ∈ Icc α₁ α₂, ∀ w ∈ Icc 0 κ,
      |f α w - ∑ s ∈ range N, φ s α * (w - aα α) ^ s| ≤ C * |w - aα α| ^ N) (N : ℕ) :
    ∃ C X : ℝ, ∀ α ∈ Icc α₁ α₂, ∀ x : ℝ, X ≤ x →
      |Real.exp (-x * bα α) * (∫ w in (0 : ℝ)..κ, Real.exp (-x * (w ^ 2 / 2 - aα α * w)) *
          f α w * w ^ (lam - 1)) -
        Real.exp (-x * bα α) * x ^ (-lam / 2) * ∑ s ∈ range N,
          φ s α * bleisteinF lam s (aα α * Real.sqrt x) * x ^ (-(s : ℝ) / 2)| ≤
      C * Real.exp (-x * bα α) * x ^ (-(lam + N) / 2) *
        ∫ τ in Ioi (0 : ℝ), Real.exp (-(τ ^ 2 / 2) + aα α * Real.sqrt x * τ) *
          |τ - aα α * Real.sqrt x| ^ N * τ ^ (lam - 1) := by
  sorry

end Bleistein

section CFU

/-- DLMF 2.4.18–2.4.20 (Chester–Friedman–Ursell): if the change of variable `t = T(w)` satisfies
`p(α, T(w)) = ⅓w³ + aw² + bw + c` near `w` (2.4.18) and `∂p/∂t ≠ 0` at `T(w)`, then
`dt/dw = (w² + 2aw + b)/(∂p/∂t)`, so `f(α,w) = q(α,t) dt/dw = q(α,t)(w² + 2aw + b)/(∂p/∂t)`
(2.4.20). Here `P = p(α, ·)` and `P'` is its derivative at `T(w)`. -/
@[dlmf 2.4.E18, dlmf 2.4.E20]
theorem cfu_deriv {P T : ℂ → ℂ} {a b c w P' T' : ℂ} (hP : HasDerivAt P P' (T w))
    (hT : HasDerivAt T T' w)
    (heq : ∀ᶠ v in 𝓝 w, P (T v) = v ^ 3 / 3 + a * v ^ 2 + b * v + c) (hP' : P' ≠ 0) :
    T' = (w ^ 2 + 2 * a * w + b) / P' := by
  have h1 : HasDerivAt (P ∘ T) (P' * T') w := hP.comp w hT
  have h2 : HasDerivAt (fun v : ℂ => v ^ 3 / 3 + a * v ^ 2 + b * v + c)
      (w ^ 2 + 2 * a * w + b) w := by
    have := ((((hasDerivAt_pow 3 w).div_const 3).add
      ((hasDerivAt_pow 2 w).const_mul a)).add ((hasDerivAt_id w).const_mul b)).add_const c
    convert this using 1
    simp; ring
  have h3 := h1.unique (h2.congr_of_eventuallyEq heq)
  rw [eq_div_iff hP']
  linear_combination h3

/-- DLMF 2.4.21: the substitution `w = z^{-1/3} v - a` (here `w = εv - a` with `ε³z = 1`)
turns the cubic exponent of 2.4.19 into Airy form:
`z(⅓w³ + aw² + bw) = ⅓v³ - (a² - b) zε v + z(⅔a³ - ab)`, with `zε = z^{2/3}`. -/
@[dlmf 2.4.E19, dlmf 2.4.E21]
theorem cfu_airy_form {z ε a b v : ℂ} (hε : ε ^ 3 * z = 1) :
    z * ((ε * v - a) ^ 3 / 3 + a * (ε * v - a) ^ 2 + b * (ε * v - a)) =
      v ^ 3 / 3 - (a ^ 2 - b) * (z * ε) * v + z * (2 * a ^ 3 / 3 - a * b) := by
  linear_combination (v ^ 3 / 3) * hε

end CFU

end DLMF.AsymptoticApproximations
