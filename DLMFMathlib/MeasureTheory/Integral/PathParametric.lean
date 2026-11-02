/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Parametric integrals along paths

Differentiation under the integral sign for integrals `∫₀¹ Φ(z, C s) g(s) ds` along a path `C`
with a bounded measurable weight `g` (typically containing the derivative of a `C¹` path), and
the elementary bounds used to apply it.

## Main results

* `ContDiffOn.exists_bound_deriv_Icc_zero_one`: the derivative of a `C¹` path on `[0, 1]` is
  bounded there.
* `intervalIntegrable_zero_one_of_bound`: bounded measurable functions are interval integrable
  on `[0, 1]`.
* `hasDerivAt_intervalIntegral_mul_comp_path`: differentiation under the integral sign along a
  path, for jointly continuous `Φ` and `∂_z Φ`.
* `continuousOn_intervalIntegral_mul_comp_path`: continuity of such parametric integrals.
* `intervalIntegral_integral_swap_zero_one`: Fubini on `[0, 1]²` for a continuous kernel times
  bounded measurable weights.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

/-- The derivative of a `C¹` path on `[0, 1]` is bounded there. -/
theorem ContDiffOn.exists_bound_deriv_Icc_zero_one {C : ℝ → ℂ}
    (hC : ContDiffOn ℝ 1 C (Icc 0 1)) :
    ∃ M, ∀ s ∈ Icc (0 : ℝ) 1, ‖deriv C s‖ ≤ M := by
  have hu : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hC.continuousOn_derivWithin hu le_rfl)
  refine ⟨M, fun s hs => ?_⟩
  by_cases hd : DifferentiableAt ℝ C s
  · rw [← hd.derivWithin (hu s hs)]; exact hM s hs
  · rw [deriv_zero_of_not_differentiableAt hd, norm_zero]
    exact (norm_nonneg _).trans (hM s hs)

/-- A function that is a.e.-strongly measurable and bounded on `[0, 1]` is interval
integrable. -/
theorem intervalIntegrable_zero_one_of_bound {f : ℝ → ℂ}
    (hm : AEStronglyMeasurable f (volume.restrict (uIoc (0 : ℝ) 1))) {B : ℝ}
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, ‖f s‖ ≤ B) : IntervalIntegrable f volume 0 1 := by
  rw [intervalIntegrable_iff]
  refine ⟨hm, HasFiniteIntegral.restrict_of_bounded B ?_ ?_⟩
  · rw [uIoc_of_le zero_le_one]; exact measure_Ioc_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le zero_le_one] at hs
    exact hb s (Ioc_subset_Icc_self hs)

/-- A function continuous on `[0, 1]` is a.e.-strongly measurable on `Ι 0 1`. -/
theorem ContinuousOn.aestronglyMeasurable_uIoc_zero_one {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc 0 1)) : AEStronglyMeasurable f (volume.restrict (uIoc (0 : ℝ) 1)) :=
  (hf.mono (by rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self)).aestronglyMeasurable
    measurableSet_uIoc

/-- Differentiation under the integral along a path: for `Φ, Φ'` jointly continuous on
`U × V` with `∂_z Φ = Φ'`, a path `C` in `V` and a bounded measurable weight `g`,
`z ↦ ∫₀¹ Φ(z, C s) g(s) ds` has derivative `∫₀¹ Φ'(z, C s) g(s) ds`. -/
theorem hasDerivAt_intervalIntegral_mul_comp_path {Φ Φ' : ℂ → ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U)
    {C : ℝ → ℂ} (hCc : ContinuousOn C (Icc 0 1)) (hCV : ∀ s ∈ Icc (0 : ℝ) 1, C s ∈ V)
    {g : ℝ → ℂ} (hgm : AEStronglyMeasurable g (volume.restrict (uIoc (0 : ℝ) 1))) {M : ℝ}
    (hgM : ∀ s ∈ Icc (0 : ℝ) 1, ‖g s‖ ≤ M)
    (hΦ : ContinuousOn (fun x : ℂ × ℂ => Φ x.1 x.2) (U ×ˢ V))
    (hΦ' : ContinuousOn (fun x : ℂ × ℂ => Φ' x.1 x.2) (U ×ˢ V))
    (hd : ∀ z ∈ U, ∀ t ∈ V, HasDerivAt (fun z => Φ z t) (Φ' z t) z) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    HasDerivAt (fun z => ∫ s in (0 : ℝ)..1, Φ z (C s) * g s)
      (∫ s in (0 : ℝ)..1, Φ' z₀ (C s) * g s) z₀ := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hcb : Metric.closedBall z₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrU
  have hKc : IsCompact (Metric.closedBall z₀ (r / 2) ×ˢ (C '' Icc 0 1)) :=
    (isCompact_closedBall _ _).prod (isCompact_Icc.image_of_continuousOn hCc)
  have hKsub : Metric.closedBall z₀ (r / 2) ×ˢ (C '' Icc 0 1) ⊆ U ×ˢ V := by
    rintro ⟨x, y⟩ ⟨hx, ⟨s, hs, rfl⟩⟩; exact ⟨hcb hx, hCV s hs⟩
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hΦ'.mono hKsub)
  have hslice : ∀ {F : ℂ → ℂ → ℂ}, ContinuousOn (fun x : ℂ × ℂ => F x.1 x.2) (U ×ˢ V) →
      ∀ x ∈ U, AEStronglyMeasurable (fun s => F x (C s) * g s) (volume.restrict (uIoc (0 : ℝ) 1)) :=
    fun {F} hF x hx => (ContinuousOn.aestronglyMeasurable_uIoc_zero_one
      (hF.comp (continuousOn_const.prodMk hCc) fun s hs => ⟨hx, hCV s hs⟩)).mul hgm
  have hball : Metric.ball z₀ (r / 2) ⊆ U := Metric.ball_subset_closedBall.trans hcb
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc.image_of_continuousOn hCc).exists_bound_of_continuousOn
    ((hΦ.comp (continuousOn_const.prodMk continuousOn_id) fun y hy => ⟨hz₀, hy⟩ :
      ContinuousOn (fun y => Φ z₀ y) V).mono (by rintro _ ⟨s, hs, rfl⟩; exact hCV s hs))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hgM 0 ⟨le_rfl, zero_le_one⟩)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z s => Φ z (C s) * g s) (F' := fun z s => Φ' z (C s) * g s)
    (bound := fun _ => B * M) (Metric.ball_mem_nhds z₀ (show (0 : ℝ) < r / 2 by linarith))
    (eventually_of_mem (Metric.ball_mem_nhds z₀ (show (0 : ℝ) < r / 2 by linarith))
      fun x hx => hslice hΦ x (hball hx))
    (intervalIntegrable_zero_one_of_bound (hslice hΦ z₀ hz₀) (B := B₀ * M) fun s hs => ?_)
    (hslice hΦ' z₀ hz₀) (ae_of_all _ fun s hs x hx => ?_) intervalIntegrable_const
    (ae_of_all _ fun s hs x hx => ?_)).2
  · rw [norm_mul]
    exact mul_le_mul (hB₀ _ ⟨s, hs, rfl⟩) (hgM s hs) (norm_nonneg _)
      ((norm_nonneg _).trans (hB₀ _ ⟨s, hs, rfl⟩))
  · rw [uIoc_of_le zero_le_one] at hs
    have hs' := Ioc_subset_Icc_self hs
    rw [norm_mul]
    exact mul_le_mul (hB (x, C s) ⟨Metric.ball_subset_closedBall hx, ⟨s, hs', rfl⟩⟩) (hgM s hs')
      (norm_nonneg _) ((norm_nonneg _).trans (hB (x, C s) ⟨Metric.ball_subset_closedBall hx,
        ⟨s, hs', rfl⟩⟩))
  · rw [uIoc_of_le zero_le_one] at hs
    exact (hd x (hball hx) (C s) (hCV s (Ioc_subset_Icc_self hs))).mul_const _

/-- Continuity of parametric integrals along a path: for `Φ` jointly continuous on `S × V` with
`S` open, a path `C` in `V` and a bounded measurable weight `g`, the map
`p ↦ ∫₀¹ Φ(p, C y) g(y) dy` is continuous on `S`. -/
theorem continuousOn_intervalIntegral_mul_comp_path {P : Type*} [MetricSpace P] [ProperSpace P]
    {Φ : P → ℂ → ℂ} {S : Set P} (hS : IsOpen S) {V : Set ℂ} {C : ℝ → ℂ}
    (hCc : ContinuousOn C (Icc 0 1)) (hCV : ∀ s ∈ Icc (0 : ℝ) 1, C s ∈ V)
    {g : ℝ → ℂ} (hgm : AEStronglyMeasurable g (volume.restrict (uIoc (0 : ℝ) 1))) {M : ℝ}
    (hgM : ∀ s ∈ Icc (0 : ℝ) 1, ‖g s‖ ≤ M)
    (hΦ : ContinuousOn (fun q : P × ℂ => Φ q.1 q.2) (S ×ˢ V)) :
    ContinuousOn (fun p => ∫ y in (0 : ℝ)..1, Φ p (C y) * g y) S := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.1 hS p hp
  have hcb : Metric.closedBall p (r / 2) ⊆ S :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrS
  have hKc : IsCompact (Metric.closedBall p (r / 2) ×ˢ (C '' Icc 0 1)) :=
    (isCompact_closedBall _ _).prod (isCompact_Icc.image_of_continuousOn hCc)
  have hKsub : Metric.closedBall p (r / 2) ×ˢ (C '' Icc 0 1) ⊆ S ×ˢ V := by
    rintro ⟨x, y⟩ ⟨hx, ⟨s, hs, rfl⟩⟩; exact ⟨hcb hx, hCV s hs⟩
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hΦ.mono hKsub)
  have hball : Metric.ball p (r / 2) ⊆ S := Metric.ball_subset_closedBall.trans hcb
  have hnhds : Metric.ball p (r / 2) ∈ 𝓝 p := Metric.ball_mem_nhds p (by linarith)
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => B * M)
    (eventually_of_mem hnhds fun x hx => ?_) (eventually_of_mem hnhds fun x hx => ?_)
    intervalIntegrable_const (ae_of_all _ fun s hs => ?_)
  · exact (ContinuousOn.aestronglyMeasurable_uIoc_zero_one
      ((hΦ.comp (continuousOn_const.prodMk hCc) fun s hs => ⟨hball hx, hCV s hs⟩))).mul hgm
  · refine ae_of_all _ fun s hs => ?_
    rw [uIoc_of_le zero_le_one] at hs
    have hs' := Ioc_subset_Icc_self hs
    have hb := hB (x, C s) ⟨Metric.ball_subset_closedBall hx, ⟨s, hs', rfl⟩⟩
    rw [norm_mul]
    exact mul_le_mul hb (hgM s hs') (norm_nonneg _) ((norm_nonneg _).trans hb)
  · rw [uIoc_of_le zero_le_one] at hs
    have hs' := Ioc_subset_Icc_self hs
    have hmap : MapsTo (fun x : P => (x, C s)) S (S ×ˢ V) := fun x hx => ⟨hx, hCV s hs'⟩
    have hc : ContinuousWithinAt (fun x => Φ x (C s)) S p :=
      ContinuousWithinAt.comp (g := fun q : P × ℂ => Φ q.1 q.2) (f := fun x : P => (x, C s))
        (hΦ (p, C s) ⟨hp, hCV s hs'⟩)
        (continuousWithinAt_id.prodMk (continuousWithinAt_const (b := C s))) hmap
    exact (hc.continuousAt (hS.mem_nhds hp)).mul continuousAt_const

/-- Fubini on `[0, 1]²` for `A(x, y) g₁(x) g₂(y)` with `A` continuous and `g₁, g₂` bounded and
measurable. -/
theorem intervalIntegral_integral_swap_zero_one {A : ℝ → ℝ → ℂ}
    (hA : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1)) {g₁ g₂ : ℝ → ℂ}
    (hg₁ : AEStronglyMeasurable g₁ (volume.restrict (uIoc (0 : ℝ) 1)))
    (hg₂ : AEStronglyMeasurable g₂ (volume.restrict (uIoc (0 : ℝ) 1))) {M₁ M₂ : ℝ}
    (hM₁ : ∀ s ∈ Icc (0 : ℝ) 1, ‖g₁ s‖ ≤ M₁) (hM₂ : ∀ s ∈ Icc (0 : ℝ) 1, ‖g₂ s‖ ≤ M₂) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, A x y * g₁ x * g₂ y =
      ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, A x y * g₁ x * g₂ y := by
  simp only [intervalIntegral.integral_of_le zero_le_one]
  rw [uIoc_of_le zero_le_one] at hg₁ hg₂
  refine integral_integral_swap ?_
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hA
  have hmeasA : AEStronglyMeasurable (fun p : ℝ × ℝ => A p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hA.mono (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)).aestronglyMeasurable
      (measurableSet_Ioc.prod measurableSet_Ioc)
  refine Integrable.of_bound ((hmeasA.mul hg₁.comp_fst).mul hg₂.comp_snd) (B * M₁ * M₂) ?_
  have hmem : ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))),
      p ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  filter_upwards [hmem] with p hp
  have h1 : p.1 ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hp.1
  have h2 : p.2 ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hp.2
  have hb := hB p ⟨h1, h2⟩
  rw [show Function.uncurry (fun x y => A x y * g₁ x * g₂ y) p = A p.1 p.2 * g₁ p.1 * g₂ p.2
    from rfl, norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hb (hM₁ _ h1) (norm_nonneg _) ((norm_nonneg _).trans hb))
    (hM₂ _ h2) (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hb)
      ((norm_nonneg _).trans (hM₁ _ h1)))
