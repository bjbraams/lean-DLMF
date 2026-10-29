/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Holomorphy in parameters of series and integrals

Mathlib proves that a series of holomorphic functions of one complex variable with a summable
bound is holomorphic (`differentiableOn_tsum_of_summable_norm`), and that parametric integrals
are differentiable under bounds on the derivative
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`).
This file removes the derivative bounds in the complex setting, for a parameter in an arbitrary
complex normed space (several complex parameters at once):

* `Complex.norm_fderiv_le_of_forall_mem_ball_norm_le`: the Cauchy estimate
  `‖Df(x)‖ ≤ M / r` for `f` holomorphic and bounded by `M` on `ball x r`, obtained from the
  one-variable estimate on complex lines.
* `Complex.differentiableOn_tsum_of_locally_dominated`: a series of holomorphic functions which
  is locally dominated by summable sequences is holomorphic; the `ℕ`-indexed variant
  `Complex.differentiableOn_tsum_of_eventually_dominated` only asks for domination of a tail.
* `Complex.differentiableOn_integral_of_locally_dominated`: a parametric integral of functions
  holomorphic in a finite-dimensional complex parameter, locally dominated by integrable functions,
  is holomorphic; `Complex.differentiableOn_intervalIntegral_of_locally_dominated` and
  `Complex.differentiableOn_integral_Ioi_of_locally_dominated` are the interval and half-line forms.
* `Complex.hasFDerivAt_integral_of_locally_dominated` gives the derivative explicitly;
  `Complex.iteratedDeriv_integral_of_locally_dominated` and its interval form commute every
  parameter derivative with integration. Their bounds use Mathlib’s Cauchy estimate
  `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`.
* `Complex.differentiableOn_of_continuousOn_of_separately` (Osgood's lemma): a continuous function
  on an open subset of `ℂ × E`, `E` finite-dimensional, that is holomorphic in each variable
  separately is jointly holomorphic;
  `Complex.differentiableOn_prod_of_continuousOn_of_separately` is the case `E = ℂ`.
  The proof uses the one-variable Cauchy integral formula and the parametric-integral theorem
  above, not Hartogs' theorem.
-/

@[expose] public section

open Filter Metric MeasureTheory Set
open scoped Topology

noncomputable section

namespace Complex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Cauchy's estimate for the derivative of a holomorphic function of several complex variables:
if `f` is holomorphic on `ball x r` and bounded there by `M`, then `‖Df(x)‖ ≤ M / r`. -/
theorem norm_fderiv_le_of_forall_mem_ball_norm_le {f : E → F} {x : E} {r M : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball x r)) (hM : ∀ y ∈ ball x r, ‖f y‖ ≤ M) :
    ‖fderiv ℂ f x‖ ≤ M / r := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_ball_self hr))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hr.le) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hfx : HasFDerivAt f (fderiv ℂ f x) x :=
    (hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasFDerivAt
  -- the restriction to the complex line through `x` in direction `v`
  set g : ℂ → F := fun t => f (x + t • v) with hg
  have hmaps : ∀ {s : ℝ}, s < r → ∀ t ∈ closedBall (0 : ℂ) (s / ‖v‖), x + t • v ∈ ball x r := by
    intro s hs t ht
    rw [mem_closedBall, dist_zero_right] at ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    calc ‖t‖ * ‖v‖ ≤ s / ‖v‖ * ‖v‖ := by gcongr
      _ = s := div_mul_cancel₀ _ hv0.ne'
      _ < r := hs
  have hline : HasFDerivAt (fun t : ℂ => x + t • v)
      ((ContinuousLinearMap.id ℂ ℂ).smulRight v) 0 :=
    ((hasFDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hg0 : HasDerivAt g (fderiv ℂ f x v) 0 := by
    have := (show HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) by simpa using hfx).comp
      (0 : ℂ) hline
    show HasDerivAt (f ∘ fun t : ℂ => x + t • v) _ 0
    simpa using this.hasDerivAt
  have key : ∀ s, 0 < s → s < r → ‖fderiv ℂ f x v‖ ≤ M / s * ‖v‖ := by
    intro s hs0 hsr
    have hR : 0 < s / ‖v‖ := div_pos hs0 hv0
    have hd : DiffContOnCl ℂ g (ball (0 : ℂ) (s / ‖v‖)) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball _ hR.ne']
      intro t ht
      have hmem := hmaps hsr t ht
      exact ((hf.differentiableAt (isOpen_ball.mem_nhds hmem)).comp t
        ((differentiableAt_const x).add
          (differentiableAt_id.smul_const v))).differentiableWithinAt
    have hC : ∀ t ∈ sphere (0 : ℂ) (s / ‖v‖), ‖g t‖ ≤ M := fun t ht =>
      hM _ (hmaps hsr t (sphere_subset_closedBall ht))
    have := norm_deriv_le_of_forall_mem_sphere_norm_le hR hd hC
    rw [hg0.deriv] at this
    calc ‖fderiv ℂ f x v‖ ≤ M / (s / ‖v‖) := this
      _ = M / s * ‖v‖ := by field_simp
  -- let `s ↑ r`
  have ht : Tendsto (fun s : ℝ => M / s * ‖v‖) (𝓝[<] r) (𝓝 (M / r * ‖v‖)) :=
    ((tendsto_const_nhds.div tendsto_id hr.ne').mul_const _).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hr] with s hs using key s hs.1 hs.2

/-- On `ball x r`, a function holomorphic and bounded by `M` on `ball x (2 r)` has derivative
bounded by `M / r`. -/
theorem norm_fderiv_le_of_mem_ball_of_ball_two_mul {f : E → F} {x y : E} {r M : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball x (2 * r))) (hM : ∀ z ∈ ball x (2 * r), ‖f z‖ ≤ M)
    (hy : y ∈ ball x r) : ‖fderiv ℂ f y‖ ≤ M / r := by
  have hsub : ball y r ⊆ ball x (2 * r) := by
    intro z hz
    rw [mem_ball] at hz hy ⊢
    calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ < r + r := add_lt_add hz hy
      _ = 2 * r := by ring
  exact norm_fderiv_le_of_forall_mem_ball_norm_le hr (hf.mono hsub) fun z hz => hM z (hsub hz)

/-- A series of holomorphic functions of several complex variables, dominated near every point
of an open set by a summable sequence, is holomorphic there. This extends Mathlib's
`differentiableOn_tsum_of_summable_norm` from `ℂ` to an arbitrary complex normed space. -/
theorem differentiableOn_tsum_of_locally_dominated [CompleteSpace F] {ι : Type*} {f : ι → E → F}
    {U : Set E} (hU : IsOpen U) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hdom : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ y ∈ V, ‖f i y‖ ≤ u i) :
    DifferentiableOn ℂ (fun x => ∑' i, f i x) U := by
  intro x hx
  obtain ⟨V, hV, u, hu, hle⟩ := hdom x hx
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hU.mem_nhds hx))
  set r := ε / 2 with hr
  have hr0 : 0 < r := half_pos hε
  have h2r : 2 * r = ε := by rw [hr]; ring
  have hball : ball x (2 * r) ⊆ V ∩ U := h2r ▸ hεsub
  have hderiv : ∀ i, ∀ y ∈ ball x r, HasFDerivAt (f i) (fderiv ℂ (f i) y) y := fun i y hy =>
    ((hf i).differentiableAt (hU.mem_nhds
      (hball (ball_subset_ball (by linarith) hy)).2)).hasFDerivAt
  have hbound : ∀ i, ∀ y ∈ ball x r, ‖fderiv ℂ (f i) y‖ ≤ u i / r := fun i y hy =>
    norm_fderiv_le_of_mem_ball_of_ball_two_mul hr0
      ((hf i).mono fun z hz => (hball hz).2) (fun z hz => hle i z (hball hz).1) hy
  have hsum0 : Summable fun i => f i x :=
    Summable.of_norm_bounded hu fun i => hle i x (hball (mem_ball_self (by linarith))).1
  exact (hasFDerivAt_tsum_of_isPreconnected (hu.div_const r) isOpen_ball
    (convex_ball x r).isPreconnected (fun i y hy => hderiv i y hy) (fun i y hy => hbound i y hy)
    (mem_ball_self hr0) hsum0 (mem_ball_self hr0)).differentiableAt.differentiableWithinAt

/-- The globally dominated form of `differentiableOn_tsum_of_locally_dominated`. -/
theorem differentiable_tsum_of_locally_dominated [CompleteSpace F] {ι : Type*} {f : ι → E → F}
    (hf : ∀ i, Differentiable ℂ (f i))
    (hdom : ∀ x, ∃ V ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ y ∈ V, ‖f i y‖ ≤ u i) :
    Differentiable ℂ (fun x => ∑' i, f i x) := by
  rw [← differentiableOn_univ]
  exact differentiableOn_tsum_of_locally_dominated isOpen_univ
    (fun i => (hf i).differentiableOn) fun x _ => hdom x

/-- A variant of `differentiableOn_tsum_of_locally_dominated` for sequences, where near each point
only a tail of the series needs to be dominated. -/
theorem differentiableOn_tsum_of_eventually_dominated [CompleteSpace F] {f : ℕ → E → F}
    {U : Set E} (hU : IsOpen U) (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hdom : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, N ≤ n → ∀ y ∈ V, ‖f n y‖ ≤ u n) :
    DifferentiableOn ℂ (fun x => ∑' n, f n x) U := by
  intro x hx
  obtain ⟨V, hV, N, u, hu, hle⟩ := hdom x hx
  obtain ⟨W, hWV, hWo, hxW⟩ := _root_.mem_nhds_iff.mp hV
  have hWU : IsOpen (W ∩ U) := hWo.inter hU
  have htail : DifferentiableOn ℂ (fun y => ∑' k, f (k + N) y) (W ∩ U) :=
    differentiableOn_tsum_of_locally_dominated hWU (fun k => (hf (k + N)).mono inter_subset_right)
      fun y hy => ⟨W, hWo.mem_nhds hy.1, fun k => u (k + N),
        (summable_nat_add_iff N).mpr hu, fun k z hz => hle (k + N) (by omega) z (hWV hz)⟩
  have hsplit : ∀ y ∈ W ∩ U, (∑' n, f n y) = ∑ n ∈ Finset.range N, f n y + ∑' k, f (k + N) y := by
    intro y hy
    obtain ⟨V', hV', N', u', hu', hle'⟩ := hdom y hy.2
    have hs : Summable fun n => f n y := by
      refine (summable_nat_add_iff (max N N')).mp ?_
      refine Summable.of_norm_bounded ((summable_nat_add_iff (max N N')).mpr hu') fun k => ?_
      exact hle' _ (by omega) y (mem_of_mem_nhds hV')
    exact (hs.sum_add_tsum_nat_add N).symm
  have hfin : DifferentiableOn ℂ (fun y => ∑ n ∈ Finset.range N, f n y) (W ∩ U) :=
    DifferentiableOn.fun_sum fun n _ => (hf n).mono inter_subset_right
  exact ((hfin.add htail).congr hsplit).differentiableAt (hWU.mem_nhds ⟨hxW, hx⟩)
    |>.differentiableWithinAt

/-! ### Parametric integrals -/

section Integral

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A continuous linear map on a finite-dimensional space is the sum of the rank-one maps given by
its values on a basis. -/
theorem _root_.ContinuousLinearMap.eq_sum_smulRight_basis [FiniteDimensional ℂ E] {n : ℕ}
    (b : Module.Basis (Fin n) ℂ E) (L : E →L[ℂ] F) :
    L = ∑ i, (LinearMap.toContinuousLinearMap (b.coord i)).smulRight (L (b i)) := by
  ext y
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  nth_rewrite 1 [← b.sum_repr y]
  rw [map_sum]
  simp only [map_smul]

/-- The derivative in a finite-dimensional complex parameter of an almost everywhere
differentiable family of strongly measurable functions is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_fderiv_param [FiniteDimensional ℂ E] {Φ : E → α → F} {x : E}
    {U : Set E} (hU : U ∈ 𝓝 x) (hmeas : ∀ y ∈ U, AEStronglyMeasurable (Φ y) μ)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableAt ℂ (Φ · a) x) :
    AEStronglyMeasurable (fun a => fderiv ℂ (Φ · a) x) μ := by
  classical
  -- directional derivatives are a.e. limits of difference quotients
  have hdir : ∀ v : E, AEStronglyMeasurable (fun a => fderiv ℂ (Φ · a) x v) μ := by
    intro v
    set q : ℂ → α → F := fun t a =>
      if x + t • v ∈ U then t⁻¹ • (Φ (x + t • v) a - Φ x a) else 0 with hq
    have hxU : x ∈ U := mem_of_mem_nhds hU
    refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ)) (f := q) (fun t => ?_) ?_
    · by_cases ht : x + t • v ∈ U
      · simp only [hq, ht, ite_true]
        exact ((hmeas _ ht).sub (hmeas x hxU)).const_smul _
      · simp only [hq, ht, ite_false]
        exact aestronglyMeasurable_const
    · filter_upwards [hdiff] with a ha
      have hline : HasDerivAt (fun t : ℂ => Φ (x + t • v) a) (fderiv ℂ (Φ · a) x v) 0 := by
        have h1 : HasFDerivAt (fun t : ℂ => x + t • v)
            ((ContinuousLinearMap.id ℂ ℂ).smulRight v) 0 :=
          ((hasFDerivAt_id (0 : ℂ)).smul_const v).const_add x
        have := (show HasFDerivAt (Φ · a) (fderiv ℂ (Φ · a) x) (x + (0 : ℂ) • v) by
          simpa using ha.hasFDerivAt).comp (0 : ℂ) h1
        show HasDerivAt ((Φ · a) ∘ fun t : ℂ => x + t • v) _ 0
        simpa using this.hasDerivAt
      have hsl := hline.tendsto_slope_zero
      simp only [zero_add, zero_smul, add_zero] at hsl
      refine hsl.congr' ?_
      have hev : ∀ᶠ t in 𝓝 (0 : ℂ), x + t • v ∈ U := by
        have hc : Continuous fun t : ℂ => x + t • v := by fun_prop
        have := hc.continuousAt (x := 0) (by simpa using hU)
        exact this
      filter_upwards [nhdsWithin_le_nhds hev] with t ht
      simp only [hq, ht, ite_true]
  set b := Module.finBasis ℂ E
  have heq : (fun a => fderiv ℂ (Φ · a) x) = fun a =>
      ∑ i, ContinuousLinearMap.smulRightL ℂ E F (LinearMap.toContinuousLinearMap (b.coord i))
        (fderiv ℂ (Φ · a) x (b i)) := by
    funext a
    conv_lhs => rw [ContinuousLinearMap.eq_sum_smulRight_basis b (fderiv ℂ (Φ · a) x)]
    rfl
  rw [heq]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.continuous _).comp_aestronglyMeasurable (hdir (b i))

/-- Local integrable domination controls the parameter derivative and permits its integration. -/
private theorem integrable_fderiv_and_hasFDerivAt_integral [FiniteDimensional ℂ E]
    {Φ : E → α → F} {U : Set E} (hU : IsOpen U)
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (Φ x) μ)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (Φ · a) U)
    (hdom : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ g : α → ℝ, Integrable g μ ∧
      ∀ᵐ a ∂μ, ∀ y ∈ V, ‖Φ y a‖ ≤ g a)
    {x : E} (hx : x ∈ U) :
    Integrable (fun a => fderiv ℂ (Φ · a) x) μ ∧
      HasFDerivAt (fun x => ∫ a, Φ x a ∂μ) (∫ a, fderiv ℂ (Φ · a) x ∂μ) x := by
  obtain ⟨V, hV, g, hg, hle⟩ := hdom x hx
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hU.mem_nhds hx))
  set r := ε / 2 with hr
  have hr0 : 0 < r := half_pos hε
  have h2r : 2 * r = ε := by rw [hr]; ring
  have hball : ball x (2 * r) ⊆ V ∩ U := h2r ▸ hεsub
  have hsU : ball x r ⊆ U := fun y hy => (hball (ball_subset_ball (by linarith) hy)).2
  have hxV : x ∈ V := (hball (mem_ball_self (by linarith))).1
  have hint : Integrable (Φ x) μ :=
    hg.mono' (hmeas x hx) (by filter_upwards [hle] with a ha using ha x hxV)
  have hderiv : ∀ᵐ a ∂μ, ∀ y ∈ ball x r, HasFDerivAt (Φ · a) (fderiv ℂ (Φ · a) y) y := by
    filter_upwards [hdiff] with a ha y hy
    exact (ha.differentiableAt (hU.mem_nhds (hsU hy))).hasFDerivAt
  have hbound : ∀ᵐ a ∂μ, ∀ y ∈ ball x r, ‖fderiv ℂ (Φ · a) y‖ ≤ g a / r := by
    filter_upwards [hdiff, hle] with a ha hla y hy
    exact norm_fderiv_le_of_mem_ball_of_ball_two_mul hr0 (ha.mono fun z hz => (hball hz).2)
      (fun z hz => hla z (hball hz).1) hy
  have hF'meas : AEStronglyMeasurable (fun a => fderiv ℂ (Φ · a) x) μ :=
    aestronglyMeasurable_fderiv_param (hU.mem_nhds hx) hmeas
      (by filter_upwards [hdiff] with a ha using ha.differentiableAt (hU.mem_nhds hx))
  have hFmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (Φ y) μ := by
    filter_upwards [hU.mem_nhds hx] with y hy using hmeas y hy
  have hint' : Integrable (fun a => fderiv ℂ (Φ · a) x) μ :=
    (hg.div_const r).mono' hF'meas (by
      filter_upwards [hbound] with a ha using ha x (mem_ball_self hr0))
  refine ⟨hint', ?_⟩
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds x hr0) hFmeas hint
    hF'meas hbound (hg.div_const r) hderiv)


/-- The parameter derivative of a locally dominated holomorphic family is integrable. -/
theorem integrable_fderiv_of_locally_dominated [FiniteDimensional ℂ E]
    {Φ : E → α → F} {U : Set E} (hU : IsOpen U)
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (Φ x) μ)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (Φ · a) U)
    (hdom : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ g : α → ℝ, Integrable g μ ∧
      ∀ᵐ a ∂μ, ∀ y ∈ V, ‖Φ y a‖ ≤ g a)
    {x : E} (hx : x ∈ U) :
    Integrable (fun a => fderiv ℂ (Φ · a) x) μ :=
  (integrable_fderiv_and_hasFDerivAt_integral hU hmeas hdiff hdom hx).1

/-- The Fréchet derivative of a locally dominated holomorphic integral is the integral of the
derivatives. -/
theorem hasFDerivAt_integral_of_locally_dominated [FiniteDimensional ℂ E]
    {Φ : E → α → F} {U : Set E} (hU : IsOpen U)
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (Φ x) μ)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (Φ · a) U)
    (hdom : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ g : α → ℝ, Integrable g μ ∧
      ∀ᵐ a ∂μ, ∀ y ∈ V, ‖Φ y a‖ ≤ g a)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun x => ∫ a, Φ x a ∂μ) (∫ a, fderiv ℂ (Φ · a) x ∂μ) x :=
  (integrable_fderiv_and_hasFDerivAt_integral hU hmeas hdiff hdom hx).2

/-- A parametric integral of functions holomorphic in a finite-dimensional complex parameter,
dominated near every point by an integrable function, is holomorphic. -/
theorem differentiableOn_integral_of_locally_dominated [FiniteDimensional ℂ E]
    {Φ : E → α → F} {U : Set E} (hU : IsOpen U)
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (Φ x) μ)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (Φ · a) U)
    (hdom : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ g : α → ℝ, Integrable g μ ∧
      ∀ᵐ a ∂μ, ∀ y ∈ V, ‖Φ y a‖ ≤ g a) :
    DifferentiableOn ℂ (fun x => ∫ a, Φ x a ∂μ) U := by
  intro x hx
  have h := hasFDerivAt_integral_of_locally_dominated hU hmeas hdiff hdom hx
  exact h.differentiableAt.differentiableWithinAt

/-- The derivative of a locally dominated holomorphic integral is the integral of the derivatives.
-/
theorem hasDerivAt_integral_of_locally_dominated [CompleteSpace F]
    {Φ : ℂ → α → F} {U : Set ℂ} (hU : IsOpen U)
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (Φ x) μ)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (Φ · a) U)
    (hdom : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ g : α → ℝ, Integrable g μ ∧
      ∀ᵐ a ∂μ, ∀ y ∈ V, ‖Φ y a‖ ≤ g a) {x : ℂ} (hx : x ∈ U) :
    HasDerivAt (fun x => ∫ a, Φ x a ∂μ) (∫ a, deriv (Φ · a) x ∂μ) x := by
  have h := integrable_fderiv_and_hasFDerivAt_integral hU hmeas hdiff hdom hx
  have hd := h.2.hasDerivAt
  simpa only [ContinuousLinearMap.integral_apply h.1, fderiv_apply_one_eq_deriv] using hd

/-- Almost every holomorphic integrand remains holomorphic after any number of parameter
derivatives. -/
private lemma ae_differentiableOn_iteratedDeriv_param [CompleteSpace F]
    {Φ : ℂ → α → F} {U : Set ℂ} (hU : IsOpen U)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (Φ · a) U) (n : ℕ) :
    ∀ᵐ a ∂μ, DifferentiableOn ℂ (iteratedDeriv n (Φ · a)) U := by
  filter_upwards [hdiff] with a ha
  rw [iteratedDeriv_eq_iterate]
  exact ((ha.analyticOnNhd hU).iterated_deriv n).differentiableOn

/-- Each parameter derivative of a measurable holomorphic family is almost everywhere strongly
measurable. -/
private lemma aestronglyMeasurable_iteratedDeriv_param [CompleteSpace F]
    {Φ : ℂ → α → F} {U : Set ℂ} (hU : IsOpen U)
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (Φ x) μ)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (Φ · a) U) (n : ℕ) :
    ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedDeriv n (Φ · a) x) μ := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hmeas
  | succ n ih =>
    intro x hx
    have hm := aestronglyMeasurable_fderiv_param (hU.mem_nhds hx) ih
      (by
        filter_upwards [ae_differentiableOn_iteratedDeriv_param hU hdiff n] with a ha
        exact ha.differentiableAt (hU.mem_nhds hx))
    simpa only [iteratedDeriv_succ, ContinuousLinearMap.apply_apply,
      fderiv_apply_one_eq_deriv] using!
      (ContinuousLinearMap.apply ℂ F (1 : ℂ)).continuous.comp_aestronglyMeasurable hm

/-- Cauchy estimates provide local integrable majorants for every parameter derivative. -/
private lemma locally_dominated_iteratedDeriv [CompleteSpace F]
    {Φ : ℂ → α → F} {U : Set ℂ} (hU : IsOpen U)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (Φ · a) U)
    (hdom : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ g : α → ℝ, Integrable g μ ∧
      ∀ᵐ a ∂μ, ∀ y ∈ V, ‖Φ y a‖ ≤ g a) (n : ℕ) :
    ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ g : α → ℝ, Integrable g μ ∧
      ∀ᵐ a ∂μ, ∀ y ∈ V, ‖iteratedDeriv n (Φ · a) y‖ ≤ g a := by
  intro x hx
  obtain ⟨V, hV, g, hg, hle⟩ := hdom x hx
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hU.mem_nhds hx))
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  refine ⟨ball x r, ball_mem_nhds x hr, fun a => (n.factorial : ℝ) * g a / r ^ n,
    (hg.const_mul _).div_const _, ?_⟩
  filter_upwards [hdiff, hle] with a ha hla y hy
  have hball : closedBall y r ⊆ V ∩ U := by
    intro w hw
    apply hεsub
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hw
    calc dist w x ≤ dist w y + dist y x := dist_triangle _ _ _
      _ < r + r := add_lt_add_of_le_of_lt hw hy
      _ = ε := by dsimp [r]; ring
  apply norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball y hr.ne']
    exact ha.mono fun w hw => (hball hw).2
  · intro w hw
    exact hla w (hball (sphere_subset_closedBall hw)).1

/-- Every parameter derivative of a locally dominated holomorphic integral commutes with
integration. -/
theorem iteratedDeriv_integral_of_locally_dominated [CompleteSpace F]
    {Φ : ℂ → α → F} {U : Set ℂ} (hU : IsOpen U)
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (Φ x) μ)
    (hdiff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (Φ · a) U)
    (hdom : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ g : α → ℝ, Integrable g μ ∧
      ∀ᵐ a ∂μ, ∀ y ∈ V, ‖Φ y a‖ ≤ g a) (n : ℕ) {x : ℂ} (hx : x ∈ U) :
    iteratedDeriv n (fun x => ∫ a, Φ x a ∂μ) x =
      ∫ a, iteratedDeriv n (Φ · a) x ∂μ := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    have he : iteratedDeriv n (fun x => ∫ a, Φ x a ∂μ) =ᶠ[𝓝 x]
        fun x => ∫ a, iteratedDeriv n (Φ · a) x ∂μ := by
      filter_upwards [hU.mem_nhds hx] with y hy using ih hy
    rw [iteratedDeriv_succ, he.deriv_eq]
    have hd := hasDerivAt_integral_of_locally_dominated hU
      (aestronglyMeasurable_iteratedDeriv_param hU hmeas hdiff n)
      (ae_differentiableOn_iteratedDeriv_param hU hdiff n)
      (locally_dominated_iteratedDeriv hU hdiff hdom n) hx
    simpa only [iteratedDeriv_succ] using hd.deriv

/-- The half-line form of `differentiableOn_integral_of_locally_dominated`. -/
theorem differentiableOn_integral_Ioi_of_locally_dominated [FiniteDimensional ℂ E]
    {Φ : E → ℝ → F} {U : Set E} (hU : IsOpen U) (c : ℝ)
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (Φ x) (volume.restrict (Ioi c)))
    (hdiff : ∀ᵐ t ∂(volume.restrict (Ioi c)), DifferentiableOn ℂ (Φ · t) U)
    (hdom : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ g : ℝ → ℝ, IntegrableOn g (Ioi c) ∧
      ∀ᵐ t ∂(volume.restrict (Ioi c)), ∀ y ∈ V, ‖Φ y t‖ ≤ g t) :
    DifferentiableOn ℂ (fun x => ∫ t in Ioi c, Φ x t) U :=
  differentiableOn_integral_of_locally_dominated hU hmeas hdiff hdom

open scoped Interval in
/-- The interval form of `differentiableOn_integral_of_locally_dominated`, with the hypotheses
taken on `Ι a b = Ioc (min a b) (max a b)` as in Mathlib's interval-integral API. -/
theorem differentiableOn_intervalIntegral_of_locally_dominated [FiniteDimensional ℂ E]
    {Φ : E → ℝ → F} {U : Set E} (hU : IsOpen U) {ν : Measure ℝ} (a b : ℝ)
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (Φ x) (ν.restrict (Ι a b)))
    (hdiff : ∀ᵐ t ∂(ν.restrict (Ι a b)), DifferentiableOn ℂ (Φ · t) U)
    (hdom : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ g : ℝ → ℝ, Integrable g (ν.restrict (Ι a b)) ∧
      ∀ᵐ t ∂(ν.restrict (Ι a b)), ∀ y ∈ V, ‖Φ y t‖ ≤ g t) :
    DifferentiableOn ℂ (fun x => ∫ t in a..b, Φ x t ∂ν) U := by
  have key : ∀ {s : Set ℝ}, s ⊆ Ι a b →
      DifferentiableOn ℂ (fun x => ∫ t in s, Φ x t ∂ν) U := by
    intro s hs
    have hle : ν.restrict s ≤ ν.restrict (Ι a b) := Measure.restrict_mono hs le_rfl
    have hac : ν.restrict s ≪ ν.restrict (Ι a b) := Measure.absolutelyContinuous_of_le hle
    refine differentiableOn_integral_of_locally_dominated hU
      (fun x hx => (hmeas x hx).mono_measure hle) (hac.ae_le hdiff) fun x hx => ?_
    obtain ⟨V, hV, g, hg, hgle⟩ := hdom x hx
    exact ⟨V, hV, g, hg.mono_measure hle, hac.ae_le hgle⟩
  have h1 := key (s := Ioc a b) Ioc_subset_uIoc
  have h2 := key (s := Ioc b a) Ioc_subset_uIoc'
  exact (h1.sub h2).congr fun x _ => rfl

/-- Every complex parameter derivative commutes with an interval integral under local integrable
domination. -/
theorem iteratedDeriv_intervalIntegral_of_locally_dominated [CompleteSpace F]
    {Φ : ℂ → ℝ → F} {U : Set ℂ} (hU : IsOpen U) {ν : Measure ℝ} (a b : ℝ)
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (Φ x) (ν.restrict (uIoc a b)))
    (hdiff : ∀ᵐ t ∂(ν.restrict (uIoc a b)), DifferentiableOn ℂ (Φ · t) U)
    (hdom : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ g : ℝ → ℝ,
      Integrable g (ν.restrict (uIoc a b)) ∧
      ∀ᵐ t ∂(ν.restrict (uIoc a b)), ∀ y ∈ V, ‖Φ y t‖ ≤ g t)
    (n : ℕ) {x : ℂ} (hx : x ∈ U) :
    iteratedDeriv n (fun x => ∫ t in a..b, Φ x t ∂ν) x =
      ∫ t in a..b, iteratedDeriv n (Φ · t) x ∂ν := by
  have hi := iteratedDeriv_integral_of_locally_dominated hU hmeas hdiff hdom n hx
  simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  split_ifs
  · simpa only [one_smul] using hi
  · simpa only [neg_one_smul, iteratedDeriv_fun_neg] using congrArg Neg.neg hi

end Integral

/-! ### Osgood's lemma -/

/-- **Osgood's lemma.** A function on an open subset of `ℂ × E`, with `E` finite-dimensional, that
is continuous and holomorphic in each of the two variables separately is jointly holomorphic.

The proof writes `f` near a point as the Cauchy integral in the first variable,
`f (z, e) = (2πi)⁻¹ ∮ (ζ - z)⁻¹ f (ζ, e) dζ`, whose integrand is jointly holomorphic in `(z, e)`;
continuity gives the local bound needed by `differentiableOn_intervalIntegral_of_locally_dominated`.
-/
theorem differentiableOn_of_continuousOn_of_separately [FiniteDimensional ℂ E] [CompleteSpace F]
    {f : ℂ × E → F} {U : Set (ℂ × E)} (hU : IsOpen U) (hc : ContinuousOn f U)
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => f (z, p.2)) p.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun e => f (p.1, e)) p.2) :
    DifferentiableOn ℂ f U := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  rintro ⟨z₀, e₀⟩ hp
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU _ hp
  set r := ε / 2 with hr
  have hr0 : 0 < r := half_pos hε
  have hmemU : ∀ z ∈ closedBall z₀ r, ∀ e ∈ closedBall e₀ r, (z, e) ∈ U := by
    intro z hz e he
    apply hεU
    rw [← ball_prod_same]
    exact ⟨closedBall_subset_ball (half_lt_self hε) hz, closedBall_subset_ball (half_lt_self hε) he⟩
  -- a bound for `f` on the compact set `sphere z₀ r × closedBall e₀ r`
  obtain ⟨M, hM⟩ :=
    ((isCompact_sphere z₀ r).prod (isCompact_closedBall e₀ r)).exists_bound_of_continuousOn
    (hc.mono fun q hq => hmemU q.1 (sphere_subset_closedBall hq.1) q.2 hq.2)
  set V : Set (ℂ × E) := ball z₀ (r / 2) ×ˢ ball e₀ r with hV
  have hVo : IsOpen V := isOpen_ball.prod isOpen_ball
  have hpV : ((z₀, e₀) : ℂ × E) ∈ V := ⟨mem_ball_self (half_pos hr0), mem_ball_self hr0⟩
  set c : ℝ → ℂ := fun θ => deriv (circleMap z₀ r) θ with hcdef
  set Φ : ℂ × E → ℝ → F := fun q θ =>
    c θ • ((circleMap z₀ r θ - q.1)⁻¹ • f (circleMap z₀ r θ, q.2)) with hΦ
  have hsph : ∀ θ, circleMap z₀ r θ ∈ sphere z₀ r := fun θ => circleMap_mem_sphere z₀ hr0.le θ
  have hne : ∀ q ∈ V, ∀ θ, circleMap z₀ r θ - q.1 ≠ 0 := by
    intro q hq θ h
    have h' : circleMap z₀ r θ = q.1 := sub_eq_zero.mp h
    have := hsph θ
    rw [h', mem_sphere] at this
    have := hq.1
    rw [mem_ball] at this
    linarith
  have hinvle : ∀ q ∈ V, ∀ θ, ‖(circleMap z₀ r θ - q.1)⁻¹‖ ≤ 2 / r := by
    intro q hq θ
    have hs : dist (circleMap z₀ r θ) z₀ = r := mem_sphere.mp (hsph θ)
    have hq1 : dist q.1 z₀ < r / 2 := hq.1
    have hd : r / 2 ≤ ‖circleMap z₀ r θ - q.1‖ := by
      rw [← dist_eq_norm]
      linarith [dist_triangle (circleMap z₀ r θ) q.1 z₀]
    rw [norm_inv]
    calc ‖circleMap z₀ r θ - q.1‖⁻¹ ≤ (r / 2)⁻¹ := inv_anti₀ (half_pos hr0) hd
      _ = 2 / r := by rw [inv_div]
  -- the Cauchy integral is jointly holomorphic
  have hG : DifferentiableOn ℂ (fun q => ∫ θ in (0 : ℝ)..2 * Real.pi, Φ q θ) V := by
    refine differentiableOn_intervalIntegral_of_locally_dominated hVo 0 (2 * Real.pi) ?_ ?_ ?_
    · intro q hq
      refine Continuous.aestronglyMeasurable ?_
      have hfc : Continuous fun θ => f (circleMap z₀ r θ, q.2) :=
        hc.comp_continuous ((continuous_circleMap z₀ r).prodMk continuous_const) fun θ =>
          hmemU _ (sphere_subset_closedBall (hsph θ)) _ (ball_subset_closedBall hq.2)
      have hcc : Continuous c := by
        simp only [hcdef, deriv_circleMap]
        fun_prop
      exact hcc.smul ((((continuous_circleMap z₀ r).sub continuous_const).inv₀
        (hne q hq)).smul hfc)
    · refine ae_of_all _ fun θ q hq => ?_
      refine DifferentiableAt.differentiableWithinAt ?_
      have hh : DifferentiableAt ℂ (fun e => f (circleMap z₀ r θ, e)) q.2 :=
        h2 (circleMap z₀ r θ, q.2) (hmemU _ (sphere_subset_closedBall (hsph θ)) _
          (ball_subset_closedBall hq.2))
      have hf2 : DifferentiableAt ℂ (fun q : ℂ × E => f (circleMap z₀ r θ, q.2)) q :=
        hh.comp q differentiableAt_snd
      have hinv : DifferentiableAt ℂ (fun q : ℂ × E => (circleMap z₀ r θ - q.1)⁻¹) q :=
        ((differentiableAt_const _).sub differentiableAt_fst).inv (hne q hq θ)
      exact (differentiableAt_const _).smul (hinv.smul hf2)
    · intro q hq
      refine ⟨V, hVo.mem_nhds hq, fun _ => r * (2 / r * M),
        (intervalIntegrable_const (μ := volume) (a := 0) (b := 2 * Real.pi)).def', ?_⟩
      refine ae_of_all _ fun θ q' hq' => ?_
      simp only [hΦ, hcdef, norm_smul]
      have hcθ : ‖deriv (circleMap z₀ r) θ‖ = r := by
        rw [deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I, mul_one, abs_of_pos hr0]
      rw [hcθ]
      have hfM : ‖f (circleMap z₀ r θ, q'.2)‖ ≤ M :=
        hM _ ⟨hsph θ, ball_subset_closedBall hq'.2⟩
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hinvle q' hq' θ) hfM (norm_nonneg _)
        (by positivity)) hr0.le
  -- the Cauchy integral formula in the first variable
  have heq : ∀ q ∈ V, f q = ((2 * Real.pi * I : ℂ))⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, Φ q θ := by
    rintro ⟨z, e⟩ hq
    have hd : DiffContOnCl ℂ (fun ζ => f (ζ, e)) (ball z₀ r) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball _ hr0.ne']
      intro ζ hζ
      exact (h1 (ζ, e) (hmemU ζ hζ e (ball_subset_closedBall hq.2))).differentiableWithinAt
    have hz : z ∈ ball z₀ r := ball_subset_ball (half_le_self hr0.le) hq.1
    have hC := hd.circleIntegral_sub_inv_smul hz
    have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, I_ne_zero]
    rw [circleIntegral] at hC
    rw [show (∫ θ in (0 : ℝ)..2 * Real.pi, Φ (z, e) θ) = (2 * Real.pi * I : ℂ) • f (z, e) from hC,
      smul_smul, inv_mul_cancel₀ h2pi, one_smul]
  have hd := ((hG.const_smul ((2 * Real.pi * I : ℂ))⁻¹).differentiableAt (hVo.mem_nhds hpV))
  exact (hd.congr_of_eventuallyEq
    (eventuallyEq_of_mem (hVo.mem_nhds hpV) heq)).differentiableWithinAt

/-- Osgood's lemma for functions of two complex variables. -/
theorem differentiableOn_prod_of_continuousOn_of_separately [CompleteSpace F]
    {f : ℂ × ℂ → F} {U : Set (ℂ × ℂ)} (hU : IsOpen U) (hc : ContinuousOn f U)
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => f (z, p.2)) p.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun w => f (p.1, w)) p.2) :
    DifferentiableOn ℂ f U :=
  differentiableOn_of_continuousOn_of_separately hU hc h1 h2

end Complex
