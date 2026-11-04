/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import DLMFMathlib.MeasureTheory.Integral.PathParametric
public import DLMF.Heun.Basic

/-!
# Heun's operator along paths; the Type II integral equation (DLMF §31.10(ii))

Lagrange's identity for Heun's operator along a `C¹` path: if `w` solves Heun's equation and
`ρ` is a branch of the weight `t^{γ-1}(t-1)^{δ-1}(t-a)^{ε-1}`, then
`(𝒟 k) w ρ - k (q w) ρ` is the derivative of the concomitant
`t(t-1)(t-a)ρ(t)(k'(t) w(t) - k(t) w'(t))`, so `∫_C (𝒟 k) w ρ dt = q ∫_C k w ρ dt` whenever the
concomitant takes equal values at the ends of the path. This is the step shared by the Type I
and Type II integral equations of DLMF §31.10. For the Type II equation the kernel equation
`(s - t)𝒟_z𝒦 = (z - t)𝒟_s𝒦 + (s - z)𝒟_t𝒦` reduces `𝒟_z` of the double integral to one such
identity along each path, with Fubini's theorem on `[0, 1]²` for the `s`-part.

## Main results

* `DLMF.Heun.integral_heunOperator_comp_path`: `∫_C (𝒟 k) w ρ dt = q ∫_C k w ρ dt` for a path
  `C` with equal end values of the concomitant.
* `DLMF.Heun.heun_integral_typeII'`: the Type II integral equation and representation,
  DLMF 31.10.12–31.10.16, without Fuchs's relation.
-/
@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Topology

noncomputable section

namespace DLMF.Heun

variable {a q α β γ δ ε : ℂ}

/-- Lagrange's identity for Heun's operator integrated along a `C¹` path `C` in `V`
(DLMF §31.10): if `w` solves Heun's equation on `V`, `ρ` has the logarithmic derivative of
`t^{γ-1}(t-1)^{δ-1}(t-a)^{ε-1}`, `k` is analytic on `V`, and the concomitant
`t(t-1)(t-a)ρ(t)(k'(t) w(t) - k(t) w'(t))` takes equal values at the ends of `C`, then
`∫_C (𝒟 k)(t) w(t) ρ(t) dt = q ∫_C k(t) w(t) ρ(t) dt`. -/
theorem integral_heunOperator_comp_path {V : Set ℂ}
    (hVs : ∀ t ∈ V, t ≠ 0 ∧ t ≠ 1 ∧ t ≠ a) {w ρ k : ℂ → ℂ} {C : ℝ → ℂ}
    (hw : IsHeunSolutionOn a q α β γ δ ε w V)
    (hρ : ∀ t ∈ V, HasDerivAt ρ (ρ t * ((γ - 1) / t + (δ - 1) / (t - 1) + (ε - 1) / (t - a))) t)
    (hk : ∀ t ∈ V, AnalyticAt ℂ k t)
    (hC : ContDiffOn ℝ 1 C (Icc 0 1)) (hCV : ∀ s ∈ Icc (0 : ℝ) 1, C s ∈ V)
    (hbd : C 1 * (C 1 - 1) * (C 1 - a) * ρ (C 1) * (deriv k (C 1) * w (C 1) -
          k (C 1) * deriv w (C 1)) =
        C 0 * (C 0 - 1) * (C 0 - a) * ρ (C 0) * (deriv k (C 0) * w (C 0) -
          k (C 0) * deriv w (C 0))) :
    ∫ s in (0 : ℝ)..1, heunOperator a α β γ δ ε k (C s) * (w (C s) * ρ (C s) * deriv C s) =
      q * ∫ s in (0 : ℝ)..1, k (C s) * (w (C s) * ρ (C s) * deriv C s) := by
  obtain ⟨MC, hMC⟩ := hC.exists_bound_deriv_Icc_zero_one
  have hCc : ContinuousOn C (Icc 0 1) := hC.continuousOn
  have hdm : AEStronglyMeasurable (deriv C) (volume.restrict (uIoc (0 : ℝ) 1)) :=
    (measurable_deriv C).aestronglyMeasurable
  have hwc : ContinuousOn w V := fun t ht =>
      (hw.differentiableAt t ht).continuousAt.continuousWithinAt
  have hρc : ContinuousOn ρ V := fun t ht => (hρ t ht).continuousAt.continuousWithinAt
  have hkc : ContinuousOn k V := fun t ht => (hk t ht).continuousAt.continuousWithinAt
  -- the integrand `k w ρ` along the path
  set F : ℂ → ℂ := fun t => k t * w t * ρ t with hF
  have hFc : ContinuousOn (fun s => F (C s)) (Icc 0 1) :=
    ((hkc.mul hwc).mul hρc).comp hCc hCV
  obtain ⟨MF, hMF⟩ := isCompact_Icc.exists_bound_of_continuousOn hFc
  have hFint : IntervalIntegrable (fun s => F (C s) * deriv C s) volume 0 1 :=
    intervalIntegrable_zero_one_of_bound
      ((ContinuousOn.aestronglyMeasurable_uIoc_zero_one hFc).mul hdm) (B := MF * MC)
      fun s hs => by
        rw [norm_mul]
        exact mul_le_mul (hMF s hs) (hMC s hs) (norm_nonneg _) ((norm_nonneg _).trans (hMF s hs))
  -- the boundary term and its derivative along `V`
  set E : ℂ → ℂ := fun t => heunOperator a α β γ δ ε k t * w t * ρ t -
    q * k t * w t * ρ t with hE
  set B : ℂ → ℂ := fun t => t * (t - 1) * (t - a) * ρ t *
    (deriv k t * w t - k t * deriv w t) with hB
  have hBd : ∀ t ∈ V, HasDerivAt B (E t) t := by
    intro t ht
    obtain ⟨ht0, ht1, hta⟩ := hVs t ht
    have hKt := hk t ht
    have hp : HasDerivAt (fun t : ℂ => t * (t - 1) * (t - a))
        ((t - 1) * (t - a) + t * (t - a) + t * (t - 1)) t := by
      have := ((hasDerivAt_id' t).fun_mul ((hasDerivAt_id' t).sub_const 1)).fun_mul
        ((hasDerivAt_id' t).sub_const a)
      exact this.congr_deriv (by ring)
    have h := (hp.fun_mul (hρ t ht)).fun_mul ((hKt.deriv.differentiableAt.hasDerivAt.fun_mul
      (hw.differentiableAt t ht).hasDerivAt).fun_sub
          (hKt.differentiableAt.hasDerivAt.fun_mul (hw.hasDerivAt_deriv t ht)))
    refine h.congr_deriv ?_
    simp only [hE, heunOperator, heunCoeffP, heunCoeffR]
    have h0 : t - 1 ≠ 0 := sub_ne_zero.2 ht1
    have h1 : t - a ≠ 0 := sub_ne_zero.2 hta
    field_simp
    ring
  have hEc : ContinuousOn E V := by
    intro t ht
    have hKt := hk t ht
    have hc : ContinuousAt (heunOperator a α β γ δ ε k) t := by
      unfold heunOperator
      have h2 : ContinuousAt (deriv (deriv k)) t := hKt.deriv.deriv.continuousAt
      have h1 : ContinuousAt (deriv k) t := hKt.deriv.continuousAt
      fun_prop
    exact ((((hc.mul (hw.differentiableAt t ht).continuousAt).mul (hρ t ht).continuousAt).sub
      (((continuousAt_const.mul hKt.continuousAt).mul (hw.differentiableAt t ht).continuousAt).mul
        (hρ t ht).continuousAt))).continuousWithinAt
  have hECc : ContinuousOn (fun s => E (C s)) (Icc 0 1) := hEc.comp hCc hCV
  obtain ⟨ME, hME⟩ := isCompact_Icc.exists_bound_of_continuousOn hECc
  have hEint : IntervalIntegrable (fun s => E (C s) * deriv C s) volume 0 1 :=
    intervalIntegrable_zero_one_of_bound
      ((ContinuousOn.aestronglyMeasurable_uIoc_zero_one hECc).mul hdm) (B := ME * MC)
      fun s hs => by
        rw [norm_mul]
        exact mul_le_mul (hME s hs) (hMC s hs) (norm_nonneg _) ((norm_nonneg _).trans (hME s hs))
  have hFTC : ∫ s in (0 : ℝ)..1, E (C s) * deriv C s = B (C 1) - B (C 0) := by
    have hBc : ContinuousOn B V := fun t ht => (hBd t ht).continuousAt.continuousWithinAt
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (hBc.comp hCc hCV) (fun s hs => ?_) hEint
    have hCd : DifferentiableAt ℝ C s :=
      (hC.differentiableOn one_ne_zero).differentiableAt (Icc_mem_nhds hs.1 hs.2)
    exact (hBd (C s) (hCV s (Ioo_subset_Icc_self hs))).comp s hCd.hasDerivAt
  have hB0 : B (C 1) - B (C 0) = 0 := sub_eq_zero.2 hbd
  have h1 : ∫ s in (0 : ℝ)..1, heunOperator a α β γ δ ε k (C s) * (w (C s) * ρ (C s) * deriv C s) =
      ∫ s in (0 : ℝ)..1, (q * (F (C s) * deriv C s) + E (C s) * deriv C s) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hE, hF]
    ring
  have h2 : ∫ s in (0 : ℝ)..1, k (C s) * (w (C s) * ρ (C s) * deriv C s) =
      ∫ s in (0 : ℝ)..1, F (C s) * deriv C s := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hF]
    ring
  rw [h1, h2, intervalIntegral.integral_add (hFint.const_mul q) hEint, hFTC, hB0, add_zero,
    intervalIntegral.integral_const_mul]

/-- A derivative of an analytic function along a family of curves through each point is
analytic. -/
private lemma analyticAt_deriv_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ} {x : E} (hF : AnalyticAt ℂ F x) (v : E) (γ : E → ℂ → E) (τ : E → ℂ)
    (hγ : ∀ p, γ p (τ p) = p) (hγd : ∀ p, HasDerivAt (γ p) v (τ p)) :
    AnalyticAt ℂ (fun p => deriv (fun u => F (γ p u)) (τ p)) x := by
  have hA := ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt (fderiv ℂ F x)).comp hF.fderiv
  apply hA.congr
  filter_upwards [hF.eventually_analyticAt] with p hp
  have h1 : HasFDerivAt F (fderiv ℂ F p) (γ p (τ p)) := by
    rw [hγ p]; exact hp.differentiableAt.hasFDerivAt
  exact ((h1.comp_hasDerivAt (τ p) (hγd p)).deriv).symm

/-- DLMF 31.10.12–31.10.16: if `w` solves Heun's equation on `V`, `ρ₁` is a branch on `V` of
`t^{γ-1}(1-t)^{δ-1}(1-t/a)^{ε-1}` (given by its logarithmic derivative), so that
`ρ(s, t) = (s - t) ρ₁(s) ρ₁(t)` is the weight 31.10.13, the kernel `𝒦(z; s, t)` satisfies
`((t-z)𝒟_s + (z-s)𝒟_t + (s-t)𝒟_z)𝒦 = 0` (31.10.14), and the concomitants
`p(t)(∂_t𝒦 w(t) - 𝒦 w'(t))` along `C₂` and `p(s)(∂_s𝒦 w(s) - 𝒦 w'(s))` along `C₁` take equal
values at the ends of the paths (31.10.15–31.10.16, `p(t) = t(t-1)(t-a)ρ₁(t)` up to a constant
factor), then `W(z) = ∫_{C₁}∫_{C₂} 𝒦(z; s, t) w(s) w(t) ρ(s, t) dt ds` (31.10.12, `s` along
`C₁`, `t` along `C₂`) is a solution of Heun's equation.
Stronger than DLMF: Fuchs's relation `α + β + 1 = γ + δ + ε` is not needed. -/
@[dlmf 31.10.E12, dlmf 31.10.E13, dlmf 31.10.E14, dlmf 31.10.E15, dlmf 31.10.E16]
theorem heun_integral_typeII' {U V : Set ℂ} (hU : IsOpen U)
    (hV : IsOpen V) (hUs : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a)
    (hVs : ∀ t ∈ V, t ≠ 0 ∧ t ≠ 1 ∧ t ≠ a) {w ρ₁ : ℂ → ℂ} {K : ℂ → ℂ → ℂ → ℂ}
    {C₁ C₂ : ℝ → ℂ} (hw : IsHeunSolutionOn a q α β γ δ ε w V)
    (hρ : ∀ t ∈ V, HasDerivAt ρ₁ (ρ₁ t * ((γ - 1) / t + (δ - 1) / (t - 1) + (ε - 1) / (t - a))) t)
    (hK : AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => K x.1 x.2.1 x.2.2) (U ×ˢ V ×ˢ V))
    (hKpde : ∀ z ∈ U, ∀ s ∈ V, ∀ t ∈ V,
      (t - z) * heunOperator a α β γ δ ε (fun s' => K z s' t) s +
        (z - s) * heunOperator a α β γ δ ε (K z s) t +
        (s - t) * heunOperator a α β γ δ ε (fun z' => K z' s t) z = 0)
    (hC₁ : ContDiffOn ℝ 1 C₁ (Icc 0 1)) (hC₂ : ContDiffOn ℝ 1 C₂ (Icc 0 1))
    (hC₁V : ∀ x ∈ Icc (0 : ℝ) 1, C₁ x ∈ V) (hC₂V : ∀ x ∈ Icc (0 : ℝ) 1, C₂ x ∈ V)
    (hbd₂ : ∀ z ∈ U, ∀ s ∈ V, let B : ℂ → ℂ := fun t => t * (t - 1) * (t - a) * ρ₁ t *
        (deriv (K z s) t * w t - K z s t * deriv w t)
      B (C₂ 1) = B (C₂ 0))
    (hbd₁ : ∀ z ∈ U, ∀ t ∈ V, let B : ℂ → ℂ := fun s => s * (s - 1) * (s - a) * ρ₁ s *
        (deriv (fun s' => K z s' t) s * w s - K z s t * deriv w s)
      B (C₁ 1) = B (C₁ 0)) :
    IsHeunSolutionOn a q α β γ δ ε
      (fun z => ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        K z (C₁ x) (C₂ y) * w (C₁ x) * w (C₂ y) * ((C₁ x - C₂ y) * ρ₁ (C₁ x) * ρ₁ (C₂ y)) *
          deriv C₁ x * deriv C₂ y) U := by
  set Ω := U ×ˢ V ×ˢ V with hΩ
  -- coordinate partial derivatives of analytic kernels are analytic
  have hdz : ∀ {G : ℂ → ℂ → ℂ → ℂ}, AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => G x.1 x.2.1 x.2.2) Ω →
      AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => deriv (fun z' => G z' x.2.1 x.2.2) x.1) Ω :=
    fun {G} hG x hx => analyticAt_deriv_curve (hG x hx) (1, 0, 0)
      (fun p u => (u, p.2.1, p.2.2)) (fun p => p.1) (fun p => rfl) fun p =>
        HasDerivAt.prodMk (hasDerivAt_id' _) (HasDerivAt.prodMk (hasDerivAt_const _ _)
          (hasDerivAt_const _ _))
  have hds : ∀ {G : ℂ → ℂ → ℂ → ℂ}, AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => G x.1 x.2.1 x.2.2) Ω →
      AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => deriv (fun s' => G x.1 s' x.2.2) x.2.1) Ω :=
    fun {G} hG x hx => analyticAt_deriv_curve (hG x hx) (0, 1, 0)
      (fun p u => (p.1, u, p.2.2)) (fun p => p.2.1) (fun p => rfl) fun p =>
        HasDerivAt.prodMk (hasDerivAt_const _ _) (HasDerivAt.prodMk (hasDerivAt_id' _)
          (hasDerivAt_const _ _))
  have hdt : ∀ {G : ℂ → ℂ → ℂ → ℂ}, AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => G x.1 x.2.1 x.2.2) Ω →
      AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => deriv (fun t' => G x.1 x.2.1 t') x.2.2) Ω :=
    fun {G} hG x hx => analyticAt_deriv_curve (hG x hx) (0, 0, 1)
      (fun p u => (p.1, p.2.1, u)) (fun p => p.2.2) (fun p => rfl) fun p =>
        HasDerivAt.prodMk (hasDerivAt_const _ _) (HasDerivAt.prodMk (hasDerivAt_const _ _)
          (hasDerivAt_id' _))
  set K1 : ℂ → ℂ → ℂ → ℂ := fun z s t => deriv (fun z' => K z' s t) z with hK1
  set K2 : ℂ → ℂ → ℂ → ℂ := fun z s t => deriv (fun z' => K1 z' s t) z with hK2
  set Ks : ℂ → ℂ → ℂ → ℂ := fun z s t => deriv (fun s' => K z s' t) s with hKs
  set Kss : ℂ → ℂ → ℂ → ℂ := fun z s t => deriv (fun s' => Ks z s' t) s with hKss
  set Kt : ℂ → ℂ → ℂ → ℂ := fun z s t => deriv (fun t' => K z s t') t with hKt
  set Ktt : ℂ → ℂ → ℂ → ℂ := fun z s t => deriv (fun t' => Kt z s t') t with hKtt
  have hA1 : AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => K1 x.1 x.2.1 x.2.2) Ω := hdz hK
  have hA2 : AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => K2 x.1 x.2.1 x.2.2) Ω := hdz hA1
  have hAs : AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => Ks x.1 x.2.1 x.2.2) Ω := hds hK
  have hAss : AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => Kss x.1 x.2.1 x.2.2) Ω := hds hAs
  have hAt : AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => Kt x.1 x.2.1 x.2.2) Ω := hdt hK
  have hAtt : AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => Ktt x.1 x.2.1 x.2.2) Ω := hdt hAt
  have hslz : ∀ {G : ℂ → ℂ → ℂ → ℂ},
      AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => G x.1 x.2.1 x.2.2) Ω →
      ∀ z ∈ U, ∀ s ∈ V, ∀ t ∈ V,
        HasDerivAt (fun z' => G z' s t) (deriv (fun z' => G z' s t) z) z :=
    fun {G} hG z hz s hs t ht => (AnalyticAt.comp (g := fun x : ℂ × ℂ × ℂ => G x.1 x.2.1 x.2.2)
      (f := fun z' : ℂ => (z', s, t)) (hG (z, s, t) ⟨hz, hs, ht⟩)
      (analyticAt_id.prod (analyticAt_const.prod analyticAt_const))).differentiableAt.hasDerivAt
  -- continuity of slices of continuous kernels
  have hcUV : ∀ {G : ℂ → ℂ → ℂ → ℂ},
      ContinuousOn (fun x : ℂ × ℂ × ℂ => G x.1 x.2.1 x.2.2) Ω → ∀ s ∈ V,
      ContinuousOn (fun x : ℂ × ℂ => G x.1 s x.2 * (s - x.2)) (U ×ˢ V) := by
    intro G hG s hs
    have h : ContinuousOn (fun x : ℂ × ℂ => G x.1 s x.2) (U ×ˢ V) :=
      hG.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
        fun x hx => ⟨hx.1, hs, hx.2⟩
    exact h.mul (continuousOn_const.sub continuous_snd.continuousOn)
  have hcUVV : ∀ {G : ℂ → ℂ → ℂ → ℂ},
      ContinuousOn (fun x : ℂ × ℂ × ℂ => G x.1 x.2.1 x.2.2) Ω →
      ContinuousOn (fun q : (ℂ × ℂ) × ℂ => G q.1.1 q.1.2 q.2 * (q.1.2 - q.2)) ((U ×ˢ V) ×ˢ V) := by
    intro G hG
    have h : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => G q.1.1 q.1.2 q.2) ((U ×ˢ V) ×ˢ V) :=
      hG.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)).continuousOn
        fun q hq => ⟨hq.1.1, hq.1.2, hq.2⟩
    exact h.mul ((continuous_snd.comp continuous_fst).continuousOn.sub continuous_snd.continuousOn)
  have hcVV : ∀ {G : ℂ → ℂ → ℂ → ℂ},
      ContinuousOn (fun x : ℂ × ℂ × ℂ => G x.1 x.2.1 x.2.2) Ω → ∀ z ∈ U,
      ContinuousOn (fun p : ℂ × ℂ => G z p.1 p.2) (V ×ˢ V) :=
    fun {G} hG z hz => hG.comp (continuous_const.prodMk continuous_id).continuousOn
      fun p hp => ⟨hz, hp.1, hp.2⟩
  -- the weights
  have hwc : ContinuousOn w V := fun t ht =>
      (hw.differentiableAt t ht).continuousAt.continuousWithinAt
  have hρc : ContinuousOn ρ₁ V := fun t ht => (hρ t ht).continuousAt.continuousWithinAt
  have hwt : ∀ {C : ℝ → ℂ}, ContDiffOn ℝ 1 C (Icc 0 1) → (∀ x ∈ Icc (0 : ℝ) 1, C x ∈ V) →
      AEStronglyMeasurable (fun x => w (C x) * ρ₁ (C x) * deriv C x)
        (volume.restrict (uIoc (0 : ℝ) 1)) ∧
      ∃ M, ∀ x ∈ Icc (0 : ℝ) 1, ‖w (C x) * ρ₁ (C x) * deriv C x‖ ≤ M := by
    intro C hC hCV
    obtain ⟨MC, hMC⟩ := hC.exists_bound_deriv_Icc_zero_one
    have hc : ContinuousOn (fun x => w (C x) * ρ₁ (C x)) (Icc 0 1) :=
      (hwc.comp hC.continuousOn hCV).mul (hρc.comp hC.continuousOn hCV)
    obtain ⟨Mw, hMw⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    refine ⟨(ContinuousOn.aestronglyMeasurable_uIoc_zero_one hc).mul
      (measurable_deriv C).aestronglyMeasurable, Mw * MC, fun x hx => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hMw x hx) (hMC x hx) (norm_nonneg _) ((norm_nonneg _).trans (hMw x hx))
  set g₁ : ℝ → ℂ := fun x => w (C₁ x) * ρ₁ (C₁ x) * deriv C₁ x with hg₁
  set g₂ : ℝ → ℂ := fun x => w (C₂ x) * ρ₁ (C₂ x) * deriv C₂ x with hg₂
  obtain ⟨hg₁m, M₁, hg₁M⟩ := hwt hC₁ hC₁V
  obtain ⟨hg₂m, M₂, hg₂M⟩ := hwt hC₂ hC₂V
  have hC₁c : ContinuousOn C₁ (Icc 0 1) := hC₁.continuousOn
  have hC₂c : ContinuousOn C₂ (Icc 0 1) := hC₂.continuousOn
  -- the inner integral and its `z`-derivatives
  have hΨc : ∀ {G : ℂ → ℂ → ℂ → ℂ},
      ContinuousOn (fun x : ℂ × ℂ × ℂ => G x.1 x.2.1 x.2.2) Ω →
      ContinuousOn (fun p : ℂ × ℂ => ∫ y in (0 : ℝ)..1, G p.1 p.2 (C₂ y) * (p.2 - C₂ y) * g₂ y)
        (U ×ˢ V) :=
    fun {G} hG => continuousOn_intervalIntegral_mul_comp_path (P := ℂ × ℂ)
      (Φ := fun p t => G p.1 p.2 t * (p.2 - t)) (hU.prod hV) hC₂c hC₂V hg₂m hg₂M (hcUVV hG)
  have hΨd : ∀ {G : ℂ → ℂ → ℂ → ℂ},
      AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => G x.1 x.2.1 x.2.2) Ω → ∀ z ∈ U, ∀ s ∈ V,
      HasDerivAt (fun z => ∫ y in (0 : ℝ)..1, G z s (C₂ y) * (s - C₂ y) * g₂ y)
        (∫ y in (0 : ℝ)..1, deriv (fun z' => G z' s (C₂ y)) z * (s - C₂ y) * g₂ y) z :=
    fun {G} hG z hz s hs => hasDerivAt_intervalIntegral_mul_comp_path
      (Φ := fun z t => G z s t * (s - t))
      (Φ' := fun z t => deriv (fun z' => G z' s t) z * (s - t)) hU hC₂c hC₂V hg₂m hg₂M
      (hcUV hG.continuousOn s hs)
      (hcUV (G := fun z s t => deriv (fun z' => G z' s t) z) (hdz hG).continuousOn s hs)
      (fun z hz t ht => (hslz hG z hz s hs t ht).mul_const _) hz
  have hWd : ∀ {G : ℂ → ℂ → ℂ → ℂ},
      AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => G x.1 x.2.1 x.2.2) Ω → ∀ z ∈ U,
      HasDerivAt (fun z => ∫ x in (0 : ℝ)..1,
          (∫ y in (0 : ℝ)..1, G z (C₁ x) (C₂ y) * (C₁ x - C₂ y) * g₂ y) * g₁ x)
        (∫ x in (0 : ℝ)..1, (∫ y in (0 : ℝ)..1,
          deriv (fun z' => G z' (C₁ x) (C₂ y)) z * (C₁ x - C₂ y) * g₂ y) * g₁ x) z :=
    fun {G} hG z hz => hasDerivAt_intervalIntegral_mul_comp_path
      (Φ := fun z s => ∫ y in (0 : ℝ)..1, G z s (C₂ y) * (s - C₂ y) * g₂ y)
      (Φ' := fun z s => ∫ y in (0 : ℝ)..1, deriv (fun z' => G z' s (C₂ y)) z * (s - C₂ y) * g₂ y)
      hU hC₁c hC₁V hg₁m hg₁M (hΨc hG.continuousOn)
      (hΨc (G := fun z s t => deriv (fun z' => G z' s t) z) (hdz hG).continuousOn)
      (fun z hz s hs => hΨd hG z hz s hs) hz
  have hfun : (fun z => ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        K z (C₁ x) (C₂ y) * w (C₁ x) * w (C₂ y) * ((C₁ x - C₂ y) * ρ₁ (C₁ x) * ρ₁ (C₂ y)) *
          deriv C₁ x * deriv C₂ y) = fun z => ∫ x in (0 : ℝ)..1,
          (∫ y in (0 : ℝ)..1, K z (C₁ x) (C₂ y) * (C₁ x - C₂ y) * g₂ y) * g₁ x := by
    funext z; congr 1; funext x
    rw [← intervalIntegral.integral_mul_const]
    congr 1; funext y; simp only [hg₁, hg₂]; ring
  rw [hfun]
  have hW1 := hWd hK
  have hW2 := hWd hA1
  refine IsLinearODE2On.mk (fun z hz => (hW1 z hz).differentiableAt) (fun z hz => ?_)
  have hev : deriv (fun z => ∫ x in (0 : ℝ)..1,
        (∫ y in (0 : ℝ)..1, K z (C₁ x) (C₂ y) * (C₁ x - C₂ y) * g₂ y) * g₁ x) =ᶠ[𝓝 z]
      fun z => ∫ x in (0 : ℝ)..1,
        (∫ y in (0 : ℝ)..1, K1 z (C₁ x) (C₂ y) * (C₁ x - C₂ y) * g₂ y) * g₁ x :=
    eventually_of_mem (hU.mem_nhds hz) fun y hy => (hW1 y hy).deriv
  refine ((hW2 z hz).congr_of_eventuallyEq hev).congr_deriv ?_
  rw [(hW1 z hz).deriv]
  obtain ⟨hz0, hz1, hza⟩ := hUs z hz
  -- integrability along the paths
  have hI : ∀ {f g : ℝ → ℂ} {M : ℝ}, ContinuousOn f (Icc 0 1) →
      AEStronglyMeasurable g (volume.restrict (uIoc (0 : ℝ) 1)) → (∀ s ∈ Icc (0 : ℝ) 1, ‖g s‖ ≤ M) →
      IntervalIntegrable (fun s => f s * g s) volume 0 1 := by
    intro f g M hf hgm hgM
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
    refine intervalIntegrable_zero_one_of_bound
      ((ContinuousOn.aestronglyMeasurable_uIoc_zero_one hf).mul hgm) (B := B * M) fun s hs => ?_
    rw [norm_mul]
    exact mul_le_mul (hB s hs) (hgM s hs) (norm_nonneg _) ((norm_nonneg _).trans (hB s hs))
  have hint₂ : ∀ {G : ℂ → ℂ → ℂ}, ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2) (V ×ˢ V) →
      ∀ s ∈ V, IntervalIntegrable (fun y => G s (C₂ y) * g₂ y) volume 0 1 :=
    fun {G} hG s hs => hI (hG.comp (continuousOn_const.prodMk hC₂c) fun y hy => ⟨hs, hC₂V y hy⟩)
      hg₂m hg₂M
  have hint₁ : ∀ {G : ℂ → ℂ → ℂ}, ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2) (V ×ˢ V) →
      ∀ t ∈ V, IntervalIntegrable (fun x => G (C₁ x) t * g₁ x) volume 0 1 :=
    fun {G} hG t ht => hI (hG.comp (hC₁c.prodMk continuousOn_const) fun x hx => ⟨hC₁V x hx, ht⟩)
      hg₁m hg₁M
  have hinner : ∀ {G : ℂ → ℂ → ℂ}, ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2) (V ×ˢ V) →
      IntervalIntegrable (fun x => (∫ y in (0 : ℝ)..1, G (C₁ x) (C₂ y) * g₂ y) * g₁ x) volume 0 1 :=
    fun {G} hG => hI ((continuousOn_intervalIntegral_mul_comp_path (P := ℂ) (Φ := G) hV hC₂c hC₂V
      hg₂m hg₂M hG).comp hC₁c hC₁V) hg₁m hg₁M
  -- the double integral as a functional of the kernel
  set Iint : (ℂ → ℂ → ℂ) → ℂ := fun G => ∫ x in (0 : ℝ)..1,
    (∫ y in (0 : ℝ)..1, G (C₁ x) (C₂ y) * g₂ y) * g₁ x with hIint
  have hcongr : ∀ {G H : ℂ → ℂ → ℂ}, (∀ s ∈ V, ∫ y in (0 : ℝ)..1, G s (C₂ y) * g₂ y =
      ∫ y in (0 : ℝ)..1, H s (C₂ y) * g₂ y) → Iint G = Iint H := by
    intro G H h
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    simp only [h (C₁ x) (hC₁V x hx)]
  have hlin : ∀ {G H : ℂ → ℂ → ℂ}, ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2) (V ×ˢ V) →
      ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (V ×ˢ V) → ∀ c d : ℂ,
      Iint (fun s t => c * G s t + d * H s t) = c * Iint G + d * Iint H := by
    intro G H hG hH c d
    have h1 : ∀ x ∈ uIcc (0 : ℝ) 1, (∫ y in (0 : ℝ)..1, (c * G (C₁ x) (C₂ y) +
        d * H (C₁ x) (C₂ y)) * g₂ y) * g₁ x =
        c * ((∫ y in (0 : ℝ)..1, G (C₁ x) (C₂ y) * g₂ y) * g₁ x) +
          d * ((∫ y in (0 : ℝ)..1, H (C₁ x) (C₂ y) * g₂ y) * g₁ x) := by
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      have e : (fun y => (c * G (C₁ x) (C₂ y) + d * H (C₁ x) (C₂ y)) * g₂ y) =
          fun y => c * (G (C₁ x) (C₂ y) * g₂ y) + d * (H (C₁ x) (C₂ y) * g₂ y) := by
        funext y; ring
      rw [e, intervalIntegral.integral_add ((hint₂ hG _ (hC₁V x hx)).const_mul c)
        ((hint₂ hH _ (hC₁V x hx)).const_mul d), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      ring
    simp only [hIint]
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_add
      ((hinner hG).const_mul c) ((hinner hH).const_mul d), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hswap : ∀ {G : ℂ → ℂ → ℂ}, ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2) (V ×ˢ V) →
      Iint G = ∫ y in (0 : ℝ)..1, (∫ x in (0 : ℝ)..1, G (C₁ x) (C₂ y) * g₁ x) * g₂ y := by
    intro G hG
    have hA : ContinuousOn (fun p : ℝ × ℝ => G (C₁ p.1) (C₂ p.2)) (Icc 0 1 ×ˢ Icc 0 1) :=
      hG.comp ((hC₁c.comp continuousOn_fst fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc 0 1) =>
        hp.1).prodMk (hC₂c.comp continuousOn_snd fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc 0 1) =>
          hp.2)) fun p hp => ⟨hC₁V _ hp.1, hC₂V _ hp.2⟩
    have h := intervalIntegral_integral_swap_zero_one (A := fun x y => G (C₁ x) (C₂ y)) hA
      hg₁m hg₂m hg₁M hg₂M
    simp only [hIint]
    have e1 : ∀ x : ℝ, (∫ y in (0 : ℝ)..1, G (C₁ x) (C₂ y) * g₂ y) * g₁ x =
        ∫ y in (0 : ℝ)..1, G (C₁ x) (C₂ y) * g₁ x * g₂ y := by
      intro x
      rw [← intervalIntegral.integral_mul_const]
      congr 1; funext y; ring
    have e2 : ∀ y : ℝ, (∫ x in (0 : ℝ)..1, G (C₁ x) (C₂ y) * g₁ x) * g₂ y =
        ∫ x in (0 : ℝ)..1, G (C₁ x) (C₂ y) * g₁ x * g₂ y := by
      intro y
      rw [← intervalIntegral.integral_mul_const]
    simp only [e1, e2]
    exact h
  -- the Lagrange identities along the two paths
  have hL₂ : ∀ s ∈ V, ∫ y in (0 : ℝ)..1, heunOperator a α β γ δ ε (K z s) (C₂ y) * g₂ y =
      q * ∫ y in (0 : ℝ)..1, K z s (C₂ y) * g₂ y := fun s hs =>
    integral_heunOperator_comp_path hVs hw hρ (fun t ht => AnalyticAt.comp
      (g := fun x : ℂ × ℂ × ℂ => K x.1 x.2.1 x.2.2) (f := fun t' : ℂ => (z, s, t'))
      (hK (z, s, t) ⟨hz, hs, ht⟩) (analyticAt_const.prod (analyticAt_const.prod analyticAt_id)))
      hC₂ hC₂V (hbd₂ z hz s hs)
  have hL₁ : ∀ t ∈ V, ∫ x in (0 : ℝ)..1,
      heunOperator a α β γ δ ε (fun s' => K z s' t) (C₁ x) * g₁ x =
      q * ∫ x in (0 : ℝ)..1, K z (C₁ x) t * g₁ x := fun t ht =>
    integral_heunOperator_comp_path hVs hw hρ (fun s hs => AnalyticAt.comp
      (g := fun x : ℂ × ℂ × ℂ => K x.1 x.2.1 x.2.2) (f := fun s' : ℂ => (z, s', t))
      (hK (z, s, t) ⟨hz, hs, ht⟩) (analyticAt_const.prod (analyticAt_id.prod analyticAt_const)))
      hC₁ hC₁V (hbd₁ z hz t ht)
  -- the three Heun operators of the kernel, and their continuity
  set Pz : ℂ := γ * (z - 1) * (z - a) + δ * z * (z - a) + ε * z * (z - 1) with hPz
  set Dz : ℂ → ℂ → ℂ := fun s t => heunOperator a α β γ δ ε (fun z' => K z' s t) z with hDz
  set Ds : ℂ → ℂ → ℂ := fun s t => heunOperator a α β γ δ ε (fun s' => K z s' t) s with hDs
  set Dt : ℂ → ℂ → ℂ := fun s t => heunOperator a α β γ δ ε (K z s) t with hDt
  have hc0 := hcVV hK.continuousOn z hz
  have hc1 := hcVV hA1.continuousOn z hz
  have hc2 := hcVV hA2.continuousOn z hz
  have hcs := hcVV hAs.continuousOn z hz
  have hcss := hcVV hAss.continuousOn z hz
  have hct := hcVV hAt.continuousOn z hz
  have hctt := hcVV hAtt.continuousOn z hz
  have eDz : ∀ s t, Dz s t = z * (z - 1) * (z - a) * K2 z s t + Pz * K1 z s t +
      α * β * z * K z s t := fun s t => rfl
  have hDzc : ContinuousOn (fun p : ℂ × ℂ => Dz p.1 p.2) (V ×ˢ V) := by
    simp only [eDz]; fun_prop
  have hDsc : ContinuousOn (fun p : ℂ × ℂ => Ds p.1 p.2) (V ×ˢ V) := by
    have e : (fun p : ℂ × ℂ => Ds p.1 p.2) = fun p => p.1 * (p.1 - 1) * (p.1 - a) *
        Kss z p.1 p.2 + (γ * (p.1 - 1) * (p.1 - a) + δ * p.1 * (p.1 - a) +
          ε * p.1 * (p.1 - 1)) * Ks z p.1 p.2 + α * β * p.1 * K z p.1 p.2 := rfl
    rw [e]; fun_prop
  have hDtc : ContinuousOn (fun p : ℂ × ℂ => Dt p.1 p.2) (V ×ˢ V) := by
    have e : (fun p : ℂ × ℂ => Dt p.1 p.2) = fun p => p.2 * (p.2 - 1) * (p.2 - a) *
        Ktt z p.1 p.2 + (γ * (p.2 - 1) * (p.2 - a) + δ * p.2 * (p.2 - a) +
          ε * p.2 * (p.2 - 1)) * Kt z p.1 p.2 + α * β * p.2 * K z p.1 p.2 := rfl
    rw [e]; fun_prop
  -- step A: `𝒟_z W` is the double integral of `(s - t) 𝒟_z 𝒦`
  have stepA : z * (z - 1) * (z - a) * Iint (fun s t => K2 z s t * (s - t)) +
      Pz * Iint (fun s t => K1 z s t * (s - t)) + α * β * z * Iint (fun s t => K z s t * (s - t)) =
      Iint (fun s t => Dz s t * (s - t)) := by
    have h1 := hlin (G := fun s t => K2 z s t * (s - t)) (H := fun s t => K1 z s t * (s - t))
      (by fun_prop) (by fun_prop) (z * (z - 1) * (z - a)) Pz
    have h2 := hlin (G := fun s t => z * (z - 1) * (z - a) * (K2 z s t * (s - t)) +
      Pz * (K1 z s t * (s - t))) (H := fun s t => K z s t * (s - t))
      (by fun_prop) (by fun_prop) 1 (α * β * z)
    have h3 := hcongr (G := fun s t => 1 * (z * (z - 1) * (z - a) * (K2 z s t * (s - t)) +
      Pz * (K1 z s t * (s - t))) + α * β * z * (K z s t * (s - t)))
      (H := fun s t => Dz s t * (s - t)) fun s _ => intervalIntegral.integral_congr fun y _ => by
        simp only [eDz]; ring
    beta_reduce at h1 h2 h3
    linear_combination -h1 - h2 + h3
  -- step B: the kernel equation splits it into an `s`-part and a `t`-part
  have stepB : Iint (fun s t => Dz s t * (s - t)) =
      Iint (fun s t => (z - t) * Ds s t) + Iint (fun s t => (s - z) * Dt s t) := by
    have h1 := hlin (G := fun s t => (z - t) * Ds s t) (H := fun s t => (s - z) * Dt s t)
      (by fun_prop) (by fun_prop) 1 1
    have h2 := hcongr (G := fun s t => Dz s t * (s - t))
      (H := fun s t => 1 * ((z - t) * Ds s t) + 1 * ((s - z) * Dt s t)) fun s hs =>
        intervalIntegral.integral_congr fun y hy => by
          rw [uIcc_of_le zero_le_one] at hy
          have hpde := hKpde z hz s hs (C₂ y) (hC₂V y hy)
          simp only [hDz, hDs, hDt]
          linear_combination g₂ y * hpde
    beta_reduce at h1 h2
    linear_combination h2 + h1
  -- step C: the `t`-part, by the Lagrange identity along `C₂`
  have stepC : Iint (fun s t => (s - z) * Dt s t) =
      Iint (fun s t => q * ((s - z) * K z s t)) := by
    refine hcongr (G := fun s t => (s - z) * Dt s t) (H := fun s t => q * ((s - z) * K z s t))
      fun s hs => ?_
    have e1 : (fun y => (s - z) * Dt s (C₂ y) * g₂ y) =
        fun y => (s - z) * (heunOperator a α β γ δ ε (K z s) (C₂ y) * g₂ y) := by
      funext y; simp only [hDt]; ring
    have e2 : (fun y => q * ((s - z) * K z s (C₂ y)) * g₂ y) =
        fun y => (q * (s - z)) * (K z s (C₂ y) * g₂ y) := by
      funext y; ring
    rw [e1, e2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hL₂ s hs]
    ring
  -- step D: the `s`-part, by Fubini and the Lagrange identity along `C₁`
  have stepD : Iint (fun s t => (z - t) * Ds s t) =
      Iint (fun s t => q * ((z - t) * K z s t)) := by
    rw [hswap (G := fun s t => (z - t) * Ds s t) (by fun_prop),
      hswap (G := fun s t => q * ((z - t) * K z s t)) (by fun_prop)]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le zero_le_one] at hy
    have e1 : (fun x => (z - C₂ y) * Ds (C₁ x) (C₂ y) * g₁ x) = fun x => (z - C₂ y) *
        (heunOperator a α β γ δ ε (fun s' => K z s' (C₂ y)) (C₁ x) * g₁ x) := by
      funext x; simp only [hDs]; ring
    have e2 : (fun x => q * ((z - C₂ y) * K z (C₁ x) (C₂ y)) * g₁ x) =
        fun x => (q * (z - C₂ y)) * (K z (C₁ x) (C₂ y) * g₁ x) := by
      funext x; ring
    rw [e1, e2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hL₁ (C₂ y) (hC₂V y hy)]
    ring
  -- step E: recombination
  have stepE : Iint (fun s t => q * ((z - t) * K z s t)) +
      Iint (fun s t => q * ((s - z) * K z s t)) = q * Iint (fun s t => K z s t * (s - t)) := by
    have h1 := hlin (G := fun s t => q * ((z - t) * K z s t))
      (H := fun s t => q * ((s - z) * K z s t)) (by fun_prop) (by fun_prop) 1 1
    have h2 := hlin (G := fun s t => K z s t * (s - t)) (H := fun s t => K z s t * (s - t))
      (by fun_prop) (by fun_prop) q 0
    have h3 := hcongr (G := fun s t => 1 * (q * ((z - t) * K z s t)) +
      1 * (q * ((s - z) * K z s t)))
      (H := fun s t => q * (K z s t * (s - t)) + 0 * (K z s t * (s - t))) fun s _ =>
        intervalIntegral.integral_congr fun y _ => by ring
    beta_reduce at h1 h2 h3
    linear_combination -h1 + h3 + h2
  have key : z * (z - 1) * (z - a) * Iint (fun s t => K2 z s t * (s - t)) +
      Pz * Iint (fun s t => K1 z s t * (s - t)) + α * β * z * Iint (fun s t => K z s t * (s - t)) =
      q * Iint (fun s t => K z s t * (s - t)) := by
    rw [stepA, stepB, stepC, stepD, stepE]
  simp only [hIint, hPz] at key
  simp only [heunCoeffP, heunCoeffR]
  have h0 : z - 1 ≠ 0 := sub_ne_zero.2 hz1
  have h1 : z - a ≠ 0 := sub_ne_zero.2 hza
  field_simp
  linear_combination key

end DLMF.Heun
