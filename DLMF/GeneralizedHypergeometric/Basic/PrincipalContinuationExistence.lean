/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuation
public import DLMF.GeneralizedHypergeometric.Basic.SeriesProperties
public import DLMF.Hypergeometric.Basic.GeneralizedIntegral
public import DLMF.Hypergeometric.Basic.GeneralizedCalculus
public import DLMF.Hypergeometric.Basic.CutPlane
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Construction of the principal continuation of `q+1Fq` (DLMF §16.2(iii))

We construct, for all complex parameters with `p = q + 1`, a continuation of the regularized
series `𝐅(a; b; z)` to the cut plane `ℂ ∖ [1, ∞)` whose restriction to the upper half-plane
continues analytically across every point of `(1, ∞)`. This gives the existence of the
normalized principal continuation `GenPrincipalContinuation`.

## Main definitions

* `eulerTransform α β G`: the Euler integral
  `(Γ(α) Γ(β-α))⁻¹ ∫₀¹ t^(α-1) (1-t)^(β-α-1) G(zt) dt` (DLMF 16.5.2).
* `HasUpperExtension V`: near every `x > 1`, the restriction of `V` to the upper half-plane
  agrees with a function holomorphic on a disk about `x`.

## Main results

* `differentiableOn_eulerTransform`: the Euler transform of a function holomorphic on the cut
  plane is holomorphic there.
* `hasUpperExtension_eulerTransform`: the Euler transform preserves continuation across the cut.
* `regularizedHGFun_contiguous_pair`, `regularizedHGFun_raise_numerator`: two contiguous
  relations of `𝐅` on the unit disk, for all parameters.
* `nonempty_genPrincipalContinuation`, `genPrincipalContinuation_exists`: existence of the
  normalized principal continuation, for all complex parameters with `p = q + 1`.
* `genRegularizedHG_eq_original`: the guarded definition agrees with the unguarded choice.
* `analyticOnNhd_genRegularizedHG`: the regularized principal function is analytic on the cut
  plane.

## Implementation notes

The proof is by induction on `q`. The case `q = 0` is `₁F₀(a;;z) = (1-z)^(-a)`. In the induction
step the Euler integral 16.5.2 adds a numerator–denominator pair `(α, β)` with
`0 < Re α < Re β`; for other parameters the two contiguous relations reduce to that region with
the shift counts `shiftB`, `shiftC` of the Gauss case (`DLMF.Hypergeometric.Basic.CutPlane`).
Holomorphy of the Euler integral on the cut plane uses that the plane is star-shaped about `0`.
For the upper boundary values the middle part of the path `[0, 1]`, where `zt` crosses `1`, is
moved into the upper half-plane by Cauchy's theorem for a rectangle; the moved integral is
holomorphic for `z` in a whole disk about the point `x > 1`.
-/

@[expose] public section

open Complex Filter Set MeasureTheory Metric
open scoped Topology Real Nat Interval

noncomputable section

namespace DLMF.Hypergeometric

/-- Parametric integrals `z ↦ ∫ₐᵇ κ t G (z γ t)` are holomorphic. -/
theorem differentiableOn_intervalIntegral_mul_comp_mul {κ γ : ℝ → ℂ} {G : ℂ → ℂ}
    {Ω U : Set ℂ} {a b : ℝ} (hab : a ≤ b) (hU : IsOpen U)
    (hκ : IntervalIntegrable κ volume a b) (hγ : ContinuousOn γ (Icc a b))
    (hG : DifferentiableOn ℂ G Ω) (hmaps : ∀ z ∈ U, ∀ t ∈ Icc a b, z * γ t ∈ Ω) :
    DifferentiableOn ℂ (fun z => ∫ t in a..b, κ t * G (z * γ t)) U := by
  have hI : Ι a b = Ioc a b := uIoc_of_le hab
  have hsub : Ioc a b ⊆ Icc a b := Ioc_subset_Icc_self
  have hκ' : IntegrableOn κ (Ioc a b) volume := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    hab).mp hκ
  have hcont : ∀ z ∈ U, ContinuousOn (fun t => G (z * γ t)) (Icc a b) := fun z hz =>
    hG.continuousOn.comp (continuousOn_const.mul hγ) fun t ht => hmaps z hz t ht
  refine Complex.differentiableOn_intervalIntegral_of_locally_dominated hU a b ?_ ?_ ?_
  · intro z hz
    rw [hI]
    exact hκ'.aestronglyMeasurable.mul
      (((hcont z hz).mono hsub).aestronglyMeasurable measurableSet_Ioc)
  · rw [hI]
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    exact (differentiableOn_const _).mul (hG.comp (differentiableOn_id.mul_const _)
      fun z hz => hmaps z hz t (hsub ht))
  · intro z₀ hz₀
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
    have hcl : closedBall z₀ (ε / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hK : ContinuousOn (fun p : ℂ × ℝ => G (p.1 * γ p.2)) (closedBall z₀ (ε / 2) ×ˢ Icc a b) :=
      hG.continuousOn.comp (continuous_fst.continuousOn.mul (hγ.comp continuous_snd.continuousOn
        fun p hp => hp.2)) fun p hp => hmaps p.1 (hcl hp.1) p.2 hp.2
    obtain ⟨M, hM⟩ :=
      ((isCompact_closedBall z₀ (ε / 2)).prod isCompact_Icc).exists_bound_of_continuousOn hK
    refine ⟨ball z₀ (ε / 2), ball_mem_nhds z₀ (half_pos hε), fun t => ‖κ t‖ * M, ?_, ?_⟩
    · rw [hI]; exact hκ'.norm.mul_const M
    · rw [hI]
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht y hy => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hM (y, t) ⟨ball_subset_closedBall hy, hsub ht⟩)
        (norm_nonneg _)

/-- The Euler weight `t^(α-1) (1-t)^(β-α-1)`, as a function of a complex variable. -/
def eulerWeight (α β t : ℂ) : ℂ := t ^ (α - 1) * (1 - t) ^ (β - α - 1)

/-- The Euler transform `(Γ(α)Γ(β-α))⁻¹ ∫₀¹ t^(α-1) (1-t)^(β-α-1) G(zt) dt`. -/
def eulerTransform (α β : ℂ) (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Gamma α * Gamma (β - α))⁻¹ * ∫ t : ℝ in (0 : ℝ)..1, eulerWeight α β t * G (z * t)

/-- The Euler weight is integrable on `[0, 1]` for `0 < Re α < Re β`. -/
theorem intervalIntegrable_eulerWeight {α β : ℂ} (ha : 0 < α.re) (hab : 0 < (β - α).re) :
    IntervalIntegrable (fun t : ℝ => eulerWeight α β t) volume 0 1 := by
  simpa [eulerWeight] using betaIntegral_convergent ha hab

/-- The cut plane is star-shaped about `0`. -/
theorem mul_ofReal_mem_cutPlane {z : ℂ} (hz : z ∈ cutPlane) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    z * t ∈ cutPlane :=
  one_sub_mul_mem_slitPlane hz ht

/-- The Euler transform of a function holomorphic on the cut plane is holomorphic there. -/
theorem differentiableOn_eulerTransform {α β : ℂ} (ha : 0 < α.re) (hab : 0 < (β - α).re)
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G cutPlane) :
    DifferentiableOn ℂ (eulerTransform α β G) cutPlane := by
  unfold eulerTransform
  refine (differentiableOn_const _).mul ?_
  exact differentiableOn_intervalIntegral_mul_comp_mul zero_le_one isOpen_cutPlane
    (intervalIntegrable_eulerWeight ha hab) continuous_ofReal.continuousOn hG
    fun z hz t ht => mul_ofReal_mem_cutPlane hz ht

/-- On the unit disk the Euler transform of the series is the series with an extra pair. -/
theorem eulerTransform_eq_regularizedHGFun {α β : ℂ} (ha : 0 < α.re) (hab : 0 < (β - α).re)
    {a b : Multiset ℂ} (hcard : a.card = b.card + 1) {G : ℂ → ℂ}
    (hG : ∀ z, ‖z‖ < 1 → G z = regularizedHGFun a b z) {z : ℂ} (hz : ‖z‖ < 1) :
    eulerTransform α β G z = regularizedHGFun (α ::ₘ a) (β ::ₘ b) z := by
  have hr : (1 : ENNReal) ≤ (regularizedHGFunSeries a b).radius :=
    Complex.radius_regularizedHGFunSeries_ge_one hcard
  have hz' : (‖z‖₊ : ENNReal) < (regularizedHGFunSeries a b).radius :=
    lt_of_lt_of_le (by exact_mod_cast hz) hr
  rw [regularizedHGFun_cons_eq_integral ha hab a b hz', eulerTransform]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [eulerWeight]
  rw [hG]
  rw [norm_mul, norm_real, Real.norm_of_nonneg ht.1]
  nlinarith [norm_nonneg z, ht.2]

/-- Local analytic continuation of the restriction to the upper half-plane across every point of
the cut `(1, ∞)`. -/
def HasUpperExtension (V : ℂ → ℂ) : Prop :=
  ∀ x : ℝ, 1 < x → ∃ g : ℂ → ℂ, ∃ R > 0, DifferentiableOn ℂ g (ball (x : ℂ) R) ∧
    ∀ w ∈ ball (x : ℂ) R, 0 < w.im → V w = g w

/-- Continuation across the cut is preserved by linear combinations with entire
coefficients. -/
theorem HasUpperExtension.linear_comb {V₁ V₂ A B : ℂ → ℂ} (h₁ : HasUpperExtension V₁)
    (h₂ : HasUpperExtension V₂) (hA : Differentiable ℂ A) (hB : Differentiable ℂ B) :
    HasUpperExtension fun z => A z * V₁ z + B z * V₂ z := by
  intro x hx
  obtain ⟨g₁, R₁, hR₁, hg₁, he₁⟩ := h₁ x hx
  obtain ⟨g₂, R₂, hR₂, hg₂, he₂⟩ := h₂ x hx
  refine ⟨fun z => A z * g₁ z + B z * g₂ z, min R₁ R₂, lt_min hR₁ hR₂, ?_, ?_⟩
  · exact (hA.differentiableOn.mul (hg₁.mono (ball_subset_ball (min_le_left _ _)))).add
      (hB.differentiableOn.mul (hg₂.mono (ball_subset_ball (min_le_right _ _))))
  · intro w hw him
    show A w * V₁ w + B w * V₂ w = A w * g₁ w + B w * g₂ w
    rw [he₁ w (ball_subset_ball (min_le_left _ _) hw) him,
      he₂ w (ball_subset_ball (min_le_right _ _) hw) him]

/-- The base case `₁F₀(a;;z) = (1-z)^(-a)` continues across the cut from above. -/
theorem hasUpperExtension_one_sub_cpow (a : ℂ) :
    HasUpperExtension fun z => (1 - z) ^ (-a) := by
  intro x hx
  refine ⟨fun w => exp ((log (w - 1) - π * I) * (-a)), x - 1, by linarith, ?_, ?_⟩
  · intro w hw
    have hre : 0 < (w - 1).re := by
      have h := (abs_re_le_norm (w - x)).trans_lt (mem_ball_iff_norm.mp hw)
      have := (abs_lt.mp h).1
      simp only [sub_re, ofReal_re, one_re] at this ⊢
      linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    have hs : w - 1 ∈ slitPlane := Or.inl hre
    exact (((differentiableAt_id.sub_const 1).clog hs).sub_const _).mul_const _ |>.cexp
  · intro w _ him
    have hne : (1 : ℂ) - w ≠ 0 := by
      intro h; have := congrArg im h; simp at this; linarith
    have him' : 0 < (w - 1).im := by simpa using him
    have harg : arg (1 - w) = arg (w - 1) - π := by
      simpa [neg_sub] using arg_neg_eq_arg_sub_pi_of_im_pos him'
    have hnorm : ‖1 - w‖ = ‖w - 1‖ := norm_sub_rev _ _
    have hlog : log (1 - w) = log (w - 1) - π * I := by
      apply Complex.ext
      · simp [log_re, hnorm]
      · simp [log_im, harg]
    simp only
    rw [cpow_def_of_ne_zero hne, hlog]

/-- The binomial series is `₁F₀`. -/
theorem regularizedHGFun_singleton_zero (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedHGFun {a} 0 z = (1 - z) ^ (-a) := by
  rw [regularizedHGFun_eq_tsum']
  refine (HasSum.tsum_eq ?_)
  convert hasSum_poch_div_factorial (β := a) hz using 2 with n
  simp [regularizedHGFunCoeff, poch]

/-! ### Contiguous relations on the unit disk -/

/-- Adding a numerator parameter `α` multiplies the coefficients by `(α)ₙ`. -/
theorem regularizedHGFunCoeff_cons_left (α : ℂ) (a b : Multiset ℂ) (n : ℕ) :
    regularizedHGFunCoeff (α ::ₘ a) b n = poch α n * regularizedHGFunCoeff a b n := by
  simp only [regularizedHGFunCoeff, Multiset.map_cons, Multiset.prod_cons, poch]
  ring

/-- For `p = q + 1` the series converges to `𝐅` on the unit disk. -/
theorem hasSum_regularizedHGFun_of_card_eq {a b : Multiset ℂ} (h : a.card = b.card + 1) {z : ℂ}
    (hz : ‖z‖ < 1) :
    HasSum (fun n => regularizedHGFunCoeff a b n * z ^ n) (regularizedHGFun a b z) := by
  have hr : (1 : ENNReal) ≤ (regularizedHGFunSeries a b).radius :=
    Complex.radius_regularizedHGFunSeries_ge_one h
  have hzr : z ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries a b).radius :=
    Metric.eball_subset_eball hr (mem_eball_one_of_norm_lt_one hz)
  simpa [Complex.regularizedHGFun, Complex.regularizedHGFunSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
    (Complex.regularizedHGFunSeries a b).hasSum (x := z) hzr

/-- The contiguous relation in a numerator–denominator pair, for all parameters. -/
theorem regularizedHGFun_contiguous_pair (α β : ℂ) (a b : Multiset ℂ)
    (h : a.card = b.card + 1) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedHGFun (α ::ₘ a) (β ::ₘ b) z =
      (β - α) * regularizedHGFun (α ::ₘ a) ((β + 1) ::ₘ b) z +
        α * regularizedHGFun ((α + 1) ::ₘ a) ((β + 1) ::ₘ b) z := by
  have hc : (α ::ₘ a).card = (β ::ₘ b).card + 1 := by simp [h]
  have hc' : (α ::ₘ a).card = ((β + 1) ::ₘ b).card + 1 := by simp [h]
  have hc'' : ((α + 1) ::ₘ a).card = ((β + 1) ::ₘ b).card + 1 := by simp [h]
  refine (hasSum_regularizedHGFun_of_card_eq hc hz).unique ?_
  convert ((hasSum_regularizedHGFun_of_card_eq hc' hz).mul_left (β - α)).add
    ((hasSum_regularizedHGFun_of_card_eq hc'' hz).mul_left α) using 1
  funext n
  simp only [regularizedHGFunCoeff_cons]
  have hΓ : (Gamma (β + n))⁻¹ = (β + n) * (Gamma (β + n + 1))⁻¹ := by
    simpa [one_div] using one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (β + n)
  have hp := poch_succ_left_mul α n
  rw [show β + 1 + (n : ℂ) = β + n + 1 by ring, div_eq_mul_inv, div_eq_mul_inv,
    div_eq_mul_inv, hΓ]
  linear_combination (-(Gamma (β + n + 1))⁻¹ * regularizedHGFunCoeff a b n * z ^ n) * hp

/-- The contiguous relation raising one numerator parameter, for all parameters. -/
theorem regularizedHGFun_raise_numerator (α : ℂ) (a b : Multiset ℂ)
    (h : a.card = b.card) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedHGFun (α ::ₘ a) b z =
      regularizedHGFun ((α + 1) ::ₘ a) b z -
        z * a.prod * regularizedHGFun ((α + 1) ::ₘ shiftParams a) (shiftParams b) z := by
  have hc : (α ::ₘ a).card = b.card + 1 := by simp [h]
  have hc' : ((α + 1) ::ₘ a).card = b.card + 1 := by simp [h]
  have hc'' : ((α + 1) ::ₘ shiftParams a).card = (shiftParams b).card + 1 := by simp [h]
  have hd := (hasSum_regularizedHGFun_of_card_eq hc hz).sub
    (hasSum_regularizedHGFun_of_card_eq hc' hz)
  set f := fun n => regularizedHGFunCoeff (α ::ₘ a) b n * z ^ n -
    regularizedHGFunCoeff ((α + 1) ::ₘ a) b n * z ^ n with hf
  have h0 : f 0 = 0 := by simp [hf, regularizedHGFunCoeff_cons_left, poch_zero]
  have hshift := (hasSum_nat_add_iff' 1).mpr hd
  simp only [Finset.range_one, Finset.sum_singleton, h0, sub_zero] at hshift
  have hR := ((hasSum_regularizedHGFun_of_card_eq hc'' hz).mul_left (-(z * a.prod)))
  have heq : (fun n => f (n + 1)) = fun n => -(z * a.prod) *
      (regularizedHGFunCoeff ((α + 1) ::ₘ shiftParams a) (shiftParams b) n * z ^ n) := by
    funext n
    simp only [hf, regularizedHGFunCoeff_cons_left]
    have h1 := regularizedHGFunCoeff_succ_deriv a b n
    have h2 := poch_succ_left α n
    have h3 := poch_succ (α + 1) n
    rw [h2, h3, pow_succ]
    linear_combination (-(poch (α + 1) n) * z ^ n * z) * h1
  rw [heq] at hshift
  have := hshift.unique hR
  linear_combination this


/-! ### Continuation of the Euler transform across the cut -/

/-- The Euler weight is holomorphic on the strip `0 < Re t < 1`. -/
theorem differentiableAt_eulerWeight (α β : ℂ) {t : ℂ} (h0 : 0 < t.re) (h1 : t.re < 1) :
    DifferentiableAt ℂ (eulerWeight α β) t := by
  have hs : t ∈ slitPlane := Or.inl h0
  have hs' : 1 - t ∈ slitPlane := Or.inl (by simp; linarith)
  exact (differentiableAt_id.cpow_const hs).mul
    ((differentiableAt_const _).sub differentiableAt_id |>.cpow_const hs')

/-- The upper half-plane lies in the cut plane. -/
theorem mem_cutPlane_of_im_pos {w : ℂ} (hw : 0 < w.im) : w ∈ cutPlane := by
  change 1 - w ∈ slitPlane
  exact Or.inr (by simp; linarith)

/-- A crude bound for `‖u + y i‖`. -/
theorem norm_ofReal_add_mul_I_le {u y : ℝ} (hu : 0 ≤ u) (hy : 0 ≤ y) :
    ‖(u : ℂ) + y * I‖ ≤ u + y := by
  refine (norm_add_le _ _).trans ?_
  simp [abs_of_nonneg hu, abs_of_nonneg hy]

/-- Gluing a local continuation `g` near `x > 1` with `G`: the glued function is holomorphic on
`ball x R ∪ ball 0 1 ∪ {Im > 0}` and agrees with `G` on the unit disk and the upper half-plane. -/
private theorem exists_glued {G g : ℂ → ℂ} (hG : DifferentiableOn ℂ G cutPlane) {x R₀ R : ℝ}
    (hg : DifferentiableOn ℂ g (ball (x : ℂ) R₀))
    (hgG : ∀ w ∈ ball (x : ℂ) R₀, 0 < w.im → G w = g w) (hRR₀ : R ≤ R₀)
    (hRx : R ≤ (x - 1) / 2) :
    ∃ Gp : ℂ → ℂ, DifferentiableOn ℂ Gp (ball (x : ℂ) R ∪ ball (0 : ℂ) 1 ∪ {w | 0 < w.im}) ∧
      (∀ w : ℂ, 0 < w.im → Gp w = G w) ∧ (∀ w : ℂ, ‖w‖ < 1 → Gp w = G w) := by
  classical
  set Gp : ℂ → ℂ := fun w => if w ∈ ball (x : ℂ) R then g w else G w with hGp
  have hGpH : ∀ w : ℂ, 0 < w.im → Gp w = G w := by
    intro w hw
    by_cases hb : w ∈ ball (x : ℂ) R
    · simp only [hGp, hb, ite_true]
      exact (hgG w (ball_subset_ball hRR₀ hb) hw).symm
    · simp only [hGp, hb, ite_false]
  have hDball : ∀ w : ℂ, ‖w‖ < 1 → w ∉ ball (x : ℂ) R := by
    intro w hw hb
    have h1 := mem_ball_iff_norm.mp hb
    have h2 : ‖(x : ℂ)‖ ≤ ‖w - x‖ + ‖w‖ := by
      calc ‖(x : ℂ)‖ = ‖-(w - x) + w‖ := by ring_nf
        _ ≤ ‖-(w - x)‖ + ‖w‖ := norm_add_le _ _
        _ = ‖w - x‖ + ‖w‖ := by rw [norm_neg]
    have hR0 : 0 ≤ R := le_trans (norm_nonneg _) h1.le
    rw [norm_real, Real.norm_of_nonneg (by linarith)] at h2
    linarith
  have hGpD : ∀ w : ℂ, ‖w‖ < 1 → Gp w = G w := by
    intro w hw
    simp only [hGp, hDball w hw, ite_false]
  refine ⟨Gp, ?_, hGpH, hGpD⟩
  intro w hw
  refine DifferentiableAt.differentiableWithinAt ?_
  rcases hw with (hw | hw) | hw
  · have hev : Gp =ᶠ[𝓝 w] g := by
      filter_upwards [isOpen_ball.mem_nhds hw] with v hv
      simp only [hGp, hv, ite_true]
    exact (hg.differentiableAt (isOpen_ball.mem_nhds
      (ball_subset_ball hRR₀ hw))).congr_of_eventuallyEq hev
  · have hw' : ‖w‖ < 1 := by simpa using hw
    have hev : Gp =ᶠ[𝓝 w] G := by
      filter_upwards [isOpen_ball.mem_nhds hw] with v hv
      exact hGpD v (by simpa using hv)
    exact (hG.differentiableAt (isOpen_cutPlane.mem_nhds
      (mem_cutPlane_of_norm_lt_one hw'))).congr_of_eventuallyEq hev
  · have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const continuous_im
    have hev : Gp =ᶠ[𝓝 w] G := by
      filter_upwards [hopen.mem_nhds hw] with v hv
      exact hGpH v hv
    exact (hG.differentiableAt (isOpen_cutPlane.mem_nhds
      (mem_cutPlane_of_im_pos hw))).congr_of_eventuallyEq hev

/-- The geometry of the deformed Euler path near a point `x > 1` of the cut. -/
private theorem exists_upper_path {x R : ℝ} (hx : 1 < x) (hR : 0 < R) (hRx : R ≤ (x - 1) / 2)
    (hR1 : R ≤ 1) :
    ∃ u₁ u₂ h r : ℝ, 0 < u₁ ∧ u₁ < u₂ ∧ u₂ < 1 ∧ 0 < h ∧ 0 < r ∧
      (∀ z ∈ ball (x : ℂ) r, 0 < z.re) ∧
      (∀ z ∈ ball (x : ℂ) r, ∀ t ∈ Icc (0 : ℝ) u₁, ‖z * (t : ℂ)‖ < 1) ∧
      (∀ z ∈ ball (x : ℂ) r, ∀ y ∈ Icc (0 : ℝ) h, ‖z * ((u₁ : ℂ) + y * I)‖ < 1) ∧
      (∀ z ∈ ball (x : ℂ) r, ∀ s ∈ Icc u₁ u₂, 0 < (z * ((s : ℂ) + h * I)).im) ∧
      (∀ z ∈ ball (x : ℂ) r, ∀ y ∈ Icc (0 : ℝ) h, z * ((u₂ : ℂ) + y * I) ∈ ball (x : ℂ) R) ∧
      (∀ z ∈ ball (x : ℂ) r, ∀ t ∈ Icc u₂ 1, z * (t : ℂ) ∈ ball (x : ℂ) R) := by
  set u₁ : ℝ := 1 / (2 * (x + 1)) with hu₁
  set h : ℝ := R / (4 * (x + 1)) with hh
  set u₂ : ℝ := 1 - R / (4 * x) with hu₂
  set r : ℝ := h * x / 4 with hr
  have hx0 : 0 < x := by linarith
  have hu₁0 : 0 < u₁ := by positivity
  have hh0 : 0 < h := by positivity
  have hr0 : 0 < r := by positivity
  have hu₁x : (x + 1) * u₁ = 1 / 2 := by rw [hu₁]; field_simp
  have hhx : (x + 1) * h = R / 4 := by rw [hh]; field_simp
  have hu₂x : x * (1 - u₂) = R / 4 := by rw [hu₂]; field_simp; ring
  have hxh : x * h ≤ R / 4 := by nlinarith
  have hhle : h ≤ 1 / 4 := by
    rw [hh, div_le_iff₀ (by positivity)]; nlinarith
  have hrR : r ≤ R / 16 := by rw [hr]; nlinarith
  have hr1 : r ≤ 1 := by linarith
  have hu₂ge : 1 / 2 ≤ u₂ := by
    rw [hu₂]
    have : R / (4 * x) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hu₁₂ : u₁ < u₂ := by
    have : u₁ < 1 / 2 := by
      rw [hu₁, div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have hu₂1 : u₂ < 1 := by
    rw [hu₂]; have : 0 < R / (4 * x) := by positivity
    linarith
  have hzb : ∀ z ∈ ball (x : ℂ) r, |z.re - x| < r ∧ |z.im| < r ∧ ‖z‖ < x + r := by
    intro z hz
    have hz' := mem_ball_iff_norm.mp hz
    refine ⟨?_, ?_, ?_⟩
    · have := (abs_re_le_norm (z - x)).trans_lt hz'
      simpa using this
    · have := (abs_im_le_norm (z - x)).trans_lt hz'
      simpa using this
    · calc ‖z‖ = ‖(z - x) + x‖ := by ring_nf
        _ ≤ ‖z - x‖ + ‖(x : ℂ)‖ := norm_add_le _ _
        _ < r + x := by rw [norm_real, Real.norm_of_nonneg hx0.le]; linarith
        _ = x + r := by ring
  refine ⟨u₁, u₂, h, r, hu₁0, hu₁₂, hu₂1, hh0, hr0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have := abs_lt.mp (hzb z hz).1
    linarith
  · intro z hz t ht
    obtain ⟨-, -, hn⟩ := hzb z hz
    rw [norm_mul, norm_real, Real.norm_of_nonneg ht.1]
    calc ‖z‖ * t ≤ (x + r) * u₁ := mul_le_mul hn.le ht.2 ht.1 (by positivity)
      _ ≤ (x + 1) * u₁ := by gcongr
      _ < 1 := by rw [hu₁x]; norm_num
  · intro z hz y hy
    obtain ⟨-, -, hn⟩ := hzb z hz
    rw [norm_mul]
    calc ‖z‖ * ‖(u₁ : ℂ) + y * I‖ ≤ (x + r) * (u₁ + h) :=
          mul_le_mul hn.le ((norm_ofReal_add_mul_I_le hu₁0.le hy.1).trans (by linarith [hy.2]))
            (norm_nonneg _) (by positivity)
      _ ≤ (x + 1) * (u₁ + h) := by gcongr
      _ < 1 := by rw [mul_add, hu₁x, hhx]; linarith
  · intro z hz s hs
    obtain ⟨hre, him, -⟩ := hzb z hz
    have hs0 : 0 ≤ s := hu₁0.le.trans hs.1
    have hs1 : s ≤ 1 := hs.2.trans hu₂1.le
    have him' : (z * ((s : ℂ) + h * I)).im = z.re * h + z.im * s := by
      simp only [mul_im, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, add_im, zero_add]
    rw [him']
    have h1 : -r ≤ z.im * s := by
      have := abs_lt.mp him
      nlinarith
    have h2 : x - r ≤ z.re := by have := abs_lt.mp hre; linarith
    have h3 : (x - r) * h ≤ z.re * h := mul_le_mul_of_nonneg_right h2 hh0.le
    have h4 : r < (x - r) * h := by
      have : r * h ≤ r * (1 / 4) := mul_le_mul_of_nonneg_left hhle hr0.le
      rw [hr] at this ⊢; nlinarith
    linarith
  · intro z hz y hy
    have hz' := mem_ball_iff_norm.mp hz
    rw [mem_ball_iff_norm]
    have heq : z * ((u₂ : ℂ) + y * I) - x =
        (z - x) * ((u₂ : ℂ) + y * I) + x * (((u₂ - 1 : ℝ) : ℂ) + y * I) := by
      push_cast; ring
    have hn1 : ‖(u₂ : ℂ) + y * I‖ ≤ 2 :=
      (norm_ofReal_add_mul_I_le (by linarith) hy.1).trans (by linarith [hy.2])
    have hn2 : ‖((u₂ - 1 : ℝ) : ℂ) + y * I‖ ≤ (1 - u₂) + h := by
      refine (norm_add_le _ _).trans ?_
      simp only [norm_real, Real.norm_eq_abs, norm_mul, norm_I, mul_one]
      rw [abs_of_nonpos (by linarith), abs_of_nonneg hy.1]
      linarith [hy.2]
    rw [heq]
    have hA : ‖(z - x) * ((u₂ : ℂ) + y * I)‖ ≤ ‖z - x‖ * 2 := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left hn1 (norm_nonneg _)
    have hB : ‖(x : ℂ) * (((u₂ - 1 : ℝ) : ℂ) + y * I)‖ ≤ x * ((1 - u₂) + h) := by
      rw [norm_mul, norm_real, Real.norm_of_nonneg hx0.le]
      exact mul_le_mul_of_nonneg_left hn2 hx0.le
    have hC : x * ((1 - u₂) + h) ≤ R / 2 := by rw [mul_add]; linarith
    calc _ ≤ ‖(z - x) * ((u₂ : ℂ) + y * I)‖ + ‖(x : ℂ) * (((u₂ - 1 : ℝ) : ℂ) + y * I)‖ :=
          norm_add_le _ _
      _ < R := by linarith
  · intro z hz t ht
    have hz' := mem_ball_iff_norm.mp hz
    rw [mem_ball_iff_norm]
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have heq : z * (t : ℂ) - x = (z - x) * t + x * ((t - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [heq]
    have hA : ‖(z - x) * (t : ℂ)‖ ≤ ‖z - x‖ := by
      rw [norm_mul, norm_real, Real.norm_of_nonneg ht0]
      exact mul_le_of_le_one_right (norm_nonneg _) ht.2
    have hB : ‖(x : ℂ) * ((t - 1 : ℝ) : ℂ)‖ ≤ x * (1 - u₂) := by
      rw [norm_mul, norm_real, norm_real, Real.norm_of_nonneg hx0.le,
        Real.norm_of_nonpos (by linarith [ht.2])]
      exact mul_le_mul_of_nonneg_left (by linarith [ht.1]) hx0.le
    calc _ ≤ ‖(z - x) * (t : ℂ)‖ + ‖(x : ℂ) * ((t - 1 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ < R := by linarith


/-- Continuation of the Euler transform across the cut, by moving the middle part of the
integration path into the upper half-plane (Cauchy's theorem for a rectangle). -/
theorem hasUpperExtension_eulerTransform {α β : ℂ} (ha : 0 < α.re) (hab : 0 < (β - α).re)
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G cutPlane) (hU : HasUpperExtension G) :
    HasUpperExtension (eulerTransform α β G) := by
  intro x hx
  obtain ⟨g, R₀, hR₀, hg, hgG⟩ := hU x hx
  set R := min R₀ (min ((x - 1) / 2) 1) with hRdef
  have hR : 0 < R := lt_min hR₀ (lt_min (by linarith) one_pos)
  have hRR₀ : R ≤ R₀ := min_le_left _ _
  have hRx : R ≤ (x - 1) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hR1 : R ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Gp, hGpd, hGpH, hGpD⟩ := exists_glued hG hg hgG hRR₀ hRx
  obtain ⟨u₁, u₂, h, r, hu₁, hu₁₂, hu₂, hh, hr, hre, hP1, hP4, hP2, hP3, hP5⟩ :=
    exists_upper_path hx hR hRx hR1
  set W := eulerWeight α β with hW
  set Ω : Set ℂ := ball (x : ℂ) R ∪ ball (0 : ℂ) 1 ∪ {w | 0 < w.im} with hΩ
  have hHopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const continuous_im
  have hWd : ∀ t : ℂ, u₁ ≤ t.re → t.re ≤ u₂ → DifferentiableAt ℂ W t := fun t h1 h2 =>
    differentiableAt_eulerWeight α β (by linarith) (by linarith)
  have hw : IntervalIntegrable (fun t : ℝ => W t) volume 0 1 :=
    intervalIntegrable_eulerWeight ha hab
  have hcontH : ∀ c : ℝ, u₁ ≤ c → c ≤ u₂ → ∀ a b : ℝ,
      ContinuousOn (fun y : ℝ => W ((c : ℂ) + y * I)) (Icc a b) := by
    intro c h1 h2 a b y _
    have hc : Continuous fun y : ℝ => (c : ℂ) + y * I := by fun_prop
    exact ((hWd _ (by simpa using h1) (by simpa using h2)).continuousAt.comp
      hc.continuousAt).continuousWithinAt
  have hcontV : ContinuousOn (fun s : ℝ => W ((s : ℂ) + h * I)) (Icc u₁ u₂) := by
    intro s hs
    have hc : Continuous fun s : ℝ => (s : ℂ) + h * I := by fun_prop
    exact ((hWd _ (by simpa using hs.1) (by simpa using hs.2)).continuousAt.comp
      hc.continuousAt).continuousWithinAt
  set Fp : ℂ → ℂ := fun z => (Gamma α * Gamma (β - α))⁻¹ *
    ((∫ t in (0 : ℝ)..u₁, W t * Gp (z * t)) +
      (∫ s in u₁..u₂, W ((s : ℂ) + h * I) * Gp (z * ((s : ℂ) + h * I))) -
      I * (∫ y in (0 : ℝ)..h, W ((u₂ : ℂ) + y * I) * Gp (z * ((u₂ : ℂ) + y * I))) +
      I * (∫ y in (0 : ℝ)..h, W ((u₁ : ℂ) + y * I) * Gp (z * ((u₁ : ℂ) + y * I))) +
      ∫ t in u₂..1, W t * Gp (z * t)) with hFp
  refine ⟨Fp, r, hr, ?_, ?_⟩
  · have d1 := differentiableOn_intervalIntegral_mul_comp_mul (κ := fun t : ℝ => W t)
      (γ := fun t : ℝ => (t : ℂ)) (Ω := Ω) (U := ball (x : ℂ) r) hu₁.le isOpen_ball
      (hw.mono_set (by
        rw [uIcc_of_le hu₁.le, uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl (by linarith)))
      continuous_ofReal.continuousOn hGpd
      (fun z hz t ht => Or.inl (Or.inr (mem_ball_zero_iff.mpr (hP1 z hz t ht))))
    have d2 := differentiableOn_intervalIntegral_mul_comp_mul
      (κ := fun s : ℝ => W ((s : ℂ) + h * I)) (γ := fun s : ℝ => (s : ℂ) + h * I) (Ω := Ω)
      (U := ball (x : ℂ) r) hu₁₂.le isOpen_ball
      (hcontV.intervalIntegrable_of_Icc hu₁₂.le) (by fun_prop) hGpd
      (fun z hz s hs => Or.inr (hP2 z hz s hs))
    have d3 := differentiableOn_intervalIntegral_mul_comp_mul
      (κ := fun y : ℝ => W ((u₂ : ℂ) + y * I)) (γ := fun y : ℝ => (u₂ : ℂ) + y * I) (Ω := Ω)
      (U := ball (x : ℂ) r) hh.le isOpen_ball
      ((hcontH u₂ hu₁₂.le le_rfl 0 h).intervalIntegrable_of_Icc hh.le) (by fun_prop) hGpd
      (fun z hz y hy => Or.inl (Or.inl (hP3 z hz y hy)))
    have d4 := differentiableOn_intervalIntegral_mul_comp_mul
      (κ := fun y : ℝ => W ((u₁ : ℂ) + y * I)) (γ := fun y : ℝ => (u₁ : ℂ) + y * I) (Ω := Ω)
      (U := ball (x : ℂ) r) hh.le isOpen_ball
      ((hcontH u₁ le_rfl hu₁₂.le 0 h).intervalIntegrable_of_Icc hh.le) (by fun_prop) hGpd
      (fun z hz y hy => Or.inl (Or.inr (mem_ball_zero_iff.mpr (hP4 z hz y hy))))
    have d5 := differentiableOn_intervalIntegral_mul_comp_mul (κ := fun t : ℝ => W t)
      (γ := fun t : ℝ => (t : ℂ)) (Ω := Ω) (U := ball (x : ℂ) r) hu₂.le isOpen_ball
      (hw.mono_set (by
        rw [uIcc_of_le hu₂.le, uIcc_of_le zero_le_one]
        exact Icc_subset_Icc (by linarith) le_rfl))
      continuous_ofReal.continuousOn hGpd
      (fun z hz t ht => Or.inl (Or.inl (hP5 z hz t ht)))
    exact (differentiableOn_const _).mul ((((d1.add d2).sub
      ((differentiableOn_const I).mul d3)).add ((differentiableOn_const I).mul d4)).add d5)
  · intro z hz him
    have hzre := hre z hz
    set f : ℂ → ℂ := fun t => W t * Gp (z * t) with hf
    have hmaps : ∀ t ∈ uIcc (0 : ℝ) 1, z * (t : ℂ) ∈ Ω := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · subst h0; left; right; simp
      · right
        show 0 < (z * (t : ℂ)).im
        simp only [mul_im, ofReal_re, ofReal_im, mul_zero, zero_add]
        positivity
    have hcongr : ∫ t in (0 : ℝ)..1, eulerWeight α β t * G (z * t) =
        ∫ t in (0 : ℝ)..1, f t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le zero_le_one] at ht
      simp only [hf]
      congr 1
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · subst h0; rw [hGpD]; simp
      · rw [hGpH]
        simp only [mul_im, ofReal_re, ofReal_im, mul_zero, zero_add]
        positivity
    have hfi : IntervalIntegrable (fun t : ℝ => f t) volume 0 1 :=
      hw.mul_continuousOn (hGpd.continuousOn.comp (by fun_prop) hmaps)
    have hfi1 : IntervalIntegrable (fun t : ℝ => f t) volume 0 u₁ := hfi.mono_set (by
      rw [uIcc_of_le hu₁.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl (by linarith))
    have hfi2 : IntervalIntegrable (fun t : ℝ => f t) volume u₁ u₂ := hfi.mono_set (by
      rw [uIcc_of_le hu₁₂.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hu₁.le hu₂.le)
    have hfi3 : IntervalIntegrable (fun t : ℝ => f t) volume u₂ 1 := hfi.mono_set (by
      rw [uIcc_of_le hu₂.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc (by linarith) le_rfl)
    have hsplit : ∫ t in (0 : ℝ)..1, f t =
        (∫ t in (0 : ℝ)..u₁, f t) + (∫ t in u₁..u₂, f t) + ∫ t in u₂..1, f t := by
      rw [intervalIntegral.integral_add_adjacent_intervals hfi1 hfi2,
        intervalIntegral.integral_add_adjacent_intervals (hfi1.trans hfi2) hfi3]
    have hd : DifferentiableOn ℂ f ([[(u₁ : ℂ).re, ((u₂ : ℂ) + h * I).re]] ×ℂ
        [[(u₁ : ℂ).im, ((u₂ : ℂ) + h * I).im]]) := by
      intro t ht
      rw [mem_reProdIm] at ht
      simp only [ofReal_re, add_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add] at ht
      rw [uIcc_of_le hu₁₂.le, uIcc_of_le hh.le] at ht
      refine DifferentiableAt.differentiableWithinAt ?_
      have hzt : 0 < (z * t).im := by
        rw [mul_im]
        have : 0 < z.im * t.re := mul_pos him (by linarith [ht.1.1])
        have : 0 ≤ z.re * t.im := mul_nonneg hzre.le ht.2.1
        linarith
      have hGat : DifferentiableAt ℂ Gp (z * t) :=
        hGpd.differentiableAt (mem_of_superset (hHopen.mem_nhds hzt) fun w hw => Or.inr hw)
      exact (hWd t ht.1.1 ht.1.2).mul (hGat.comp t (differentiableAt_id.const_mul z))
    have hrect := integral_boundary_rect_eq_zero_of_differentiableOn f (u₁ : ℂ)
      ((u₂ : ℂ) + h * I) hd
    simp only [ofReal_re, add_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, ofReal_zero, zero_mul, smul_eq_mul] at hrect
    simp only [eulerTransform, hFp]
    rw [hcongr, hsplit]
    congr 1
    simp only [hf] at hrect ⊢
    linear_combination hrect


/-! ### Existence by induction on the number of parameters -/

/-- The properties of a continuation that are carried through the induction. -/
private def GoodCont (a b : Multiset ℂ) (V : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ V cutPlane ∧ (∀ z : ℂ, ‖z‖ < 1 → V z = regularizedHGFun a b z) ∧
    HasUpperExtension V

/-- The case `q = 0`: `₁F₀(a;;z) = (1-z)^(-a)`. -/
private theorem goodCont_base (a₀ : ℂ) : GoodCont {a₀} 0 fun z => (1 - z) ^ (-a₀) := by
  refine ⟨fun z hz => ?_, fun z hz => (regularizedHGFun_singleton_zero a₀ hz).symm,
    hasUpperExtension_one_sub_cpow a₀⟩
  exact (((differentiableAt_const _).sub differentiableAt_id).cpow_const
    (mem_cutPlane.mp hz)).differentiableWithinAt

/-- The induction properties pass to linear combinations. -/
private theorem goodCont_linear_comb {a b a₁ b₁ a₂ b₂ : Multiset ℂ} {V₁ V₂ A B : ℂ → ℂ}
    (h₁ : GoodCont a₁ b₁ V₁) (h₂ : GoodCont a₂ b₂ V₂) (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B)
    (hrel : ∀ z : ℂ, ‖z‖ < 1 → regularizedHGFun a b z =
      A z * regularizedHGFun a₁ b₁ z + B z * regularizedHGFun a₂ b₂ z) :
    GoodCont a b fun z => A z * V₁ z + B z * V₂ z := by
  refine ⟨(hA.differentiableOn.mul h₁.1).add (hB.differentiableOn.mul h₂.1), fun z hz => ?_,
    h₁.2.2.linear_comb h₂.2.2 hA hB⟩
  show A z * V₁ z + B z * V₂ z = _
  rw [hrel z hz, h₁.2.1 z hz, h₂.2.1 z hz]

/-- The induction step, by induction on the shift measure of the pair `(α, β)`. -/
private theorem goodCont_step {q : ℕ}
    (ih : ∀ a b : Multiset ℂ, b.card = q → a.card = q + 1 → ∃ V, GoodCont a b V) (n : ℕ) :
    ∀ (α β : ℂ) (a b : Multiset ℂ), shiftMeasure α β ≤ n → b.card = q → a.card = q + 1 →
      ∃ V, GoodCont (α ::ₘ a) (β ::ₘ b) V := by
  induction n with
  | zero =>
    intro α β a b hn hb ha
    have h0 : shiftB α = 0 ∧ shiftC α β = 0 := by unfold shiftMeasure at hn; omega
    obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero h0.1 h0.2
    obtain ⟨G, hG⟩ := ih a b hb ha
    exact ⟨eulerTransform α β G, differentiableOn_eulerTransform (by linarith) (by linarith) hG.1,
      fun z hz => eulerTransform_eq_regularizedHGFun (by linarith) (by linarith) (by omega)
        hG.2.1 hz,
      hasUpperExtension_eulerTransform (by linarith) (by linarith) hG.1 hG.2.2⟩
  | succ n ihn =>
    intro α β a b hn hb ha
    by_cases hc : 0 < shiftC α β
    · obtain ⟨α', a', rfl⟩ : ∃ α' a', a = α' ::ₘ a' := by
        obtain ⟨α', hα'⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < a.card)
        obtain ⟨a', ha'⟩ := Multiset.exists_cons_of_mem hα'
        exact ⟨α', a', ha'⟩
      have hlt := shiftC_add_one_lt hc
      have hn' : shiftMeasure α (β + 1) ≤ n := by unfold shiftMeasure at hn ⊢; omega
      obtain ⟨V₁, hV₁⟩ := ihn α (β + 1) (α' ::ₘ a') b hn' hb ha
      obtain ⟨V₂, hV₂⟩ := ihn α (β + 1) ((α' + 1) ::ₘ a') b hn' hb (by simpa using ha)
      refine ⟨_, goodCont_linear_comb hV₁ hV₂ (differentiable_const (β - α'))
        (differentiable_const α') fun z hz => ?_⟩
      have hcard : (α ::ₘ a').card = b.card + 1 := by simp at ha ⊢; omega
      rw [Multiset.cons_swap α α', Multiset.cons_swap α (α' + 1)]
      exact regularizedHGFun_contiguous_pair α' β (α ::ₘ a') b hcard hz
    · by_cases hB : 0 < shiftB α
      · obtain ⟨hm1, hm2⟩ := shiftMeasure_b_step hc hB
        obtain ⟨V₁, hV₁⟩ := ihn (α + 1) β a b (by omega) hb ha
        obtain ⟨V₂, hV₂⟩ := ihn (α + 1) (β + 1) (shiftParams a) (shiftParams b) (by omega)
          (by simpa using hb) (by simpa using ha)
        refine ⟨_, goodCont_linear_comb hV₁ hV₂ (differentiable_const 1)
          (B := fun z => -(z * a.prod)) (by fun_prop) fun z hz => ?_⟩
        have hcard : a.card = (β ::ₘ b).card := by simp [ha, hb]
        have := regularizedHGFun_raise_numerator α a (β ::ₘ b) hcard hz
        simp only [shiftParams, Multiset.map_cons] at this ⊢
        rw [this]
        ring
      · obtain ⟨h1, h2⟩ := euler_region_of_shift_eq_zero (Nat.eq_zero_of_not_pos hB)
          (Nat.eq_zero_of_not_pos hc)
        obtain ⟨G, hG⟩ := ih a b hb ha
        exact ⟨eulerTransform α β G,
          differentiableOn_eulerTransform (by linarith) (by linarith) hG.1,
          fun z hz => eulerTransform_eq_regularizedHGFun (by linarith) (by linarith) (by omega)
            hG.2.1 hz,
          hasUpperExtension_eulerTransform (by linarith) (by linarith) hG.1 hG.2.2⟩

/-- Existence of a continuation with the induction properties, by induction on `q`. -/
private theorem exists_goodCont (q : ℕ) :
    ∀ a b : Multiset ℂ, b.card = q → a.card = q + 1 → ∃ V, GoodCont a b V := by
  induction q with
  | zero =>
    intro a b hb ha
    obtain ⟨a₀, rfl⟩ := Multiset.card_eq_one.mp ha
    rw [Multiset.card_eq_zero.mp hb]
    exact ⟨_, goodCont_base a₀⟩
  | succ q ih =>
    intro a b hb ha
    obtain ⟨β, hβ⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < b.card)
    obtain ⟨b', rfl⟩ := Multiset.exists_cons_of_mem hβ
    obtain ⟨α, hα⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < a.card)
    obtain ⟨a', rfl⟩ := Multiset.exists_cons_of_mem hα
    exact goodCont_step ih _ α β a' b' le_rfl (by simpa using hb) (by simpa using ha)

/-- Existence of the normalized principal continuation of `q+1Fq`, for all parameters. -/
theorem nonempty_genPrincipalContinuation (a b : Multiset ℂ) (h : a.card = b.card + 1) :
    Nonempty (GenPrincipalContinuation a b) := by
  classical
  obtain ⟨V, hVd, hVg, hVu⟩ := exists_goodCont b.card a b rfl h
  let value : ℂ → ℂ := fun z =>
    if z ∈ cutPlane then V z
    else if hz : 1 < z.re then Classical.choose (hVu z.re hz) z
    else regularizedHGFun a b 1
  have hval : ∀ z ∈ cutPlane, value z = V z := fun z hz => by simp only [value, hz, ite_true]
  have hnot : ∀ x : ℝ, (x : ℂ) ∉ cutPlane ↔ 1 ≤ x := by
    intro x
    rw [mem_cutPlane, mem_slitPlane_iff_not_le_zero, not_not, Complex.le_def]
    simp
  refine ⟨{ value := value, analytic := ?_, germ := ?_, upper_boundary := ?_, one := ?_ }⟩
  · exact (hVd.analyticOnNhd isOpen_cutPlane).congr isOpen_cutPlane
      fun z hz => (hval z hz).symm
  · intro z hz
    rw [hval z (mem_cutPlane_of_norm_lt_one hz), hVg z hz]
  · intro x hx
    have hx' : (x : ℂ) ∉ cutPlane := (hnot x).mpr hx.le
    have hxre : 1 < (x : ℂ).re := by simpa using hx
    obtain ⟨R, hR, hgd, hgV⟩ := Classical.choose_spec (hVu x hx)
    have hvx : value x = Classical.choose (hVu x hx) x := by
      simp only [value, hx', ite_false, ofReal_re, hx, dite_true]
    rw [hvx]
    have hcont : ContinuousAt (Classical.choose (hVu x hx)) (x : ℂ) :=
      (hgd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))).continuousAt
    refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    have hmem : {w : ℂ | 0 < w.im} ∩ ball (x : ℂ) R ∈ 𝓝[{w : ℂ | 0 < w.im}] (x : ℂ) :=
      inter_mem_nhdsWithin _ (isOpen_ball.mem_nhds (mem_ball_self hR))
    filter_upwards [hmem] with w hw
    rw [hval w (mem_cutPlane_of_im_pos hw.1), hgV w hw.2 hw.1]
  · have h1 : (1 : ℂ) ∉ cutPlane := by simpa using (hnot 1).mpr le_rfl
    simp [value, h1]

/-- Existence of principal continuation for all regularized parameters, including Gamma zeros. -/
theorem genPrincipalContinuation_exists (a b : Multiset ℂ) (h : a.card = b.card + 1) :
    Nonempty (GenPrincipalContinuation a b) :=
  nonempty_genPrincipalContinuation a b h

/-- The guarded definition preserves the previous choice of continuation, assuming
exactly the recorded existence theorem. This does not prove existence. -/
theorem genRegularizedHG_eq_original (a b : Multiset ℂ) (z : ℂ) :
    genRegularizedHG a b z =
      if h : a.card = b.card + 1 then
        (Classical.choice (genPrincipalContinuation_exists a b h)).value z
      else Complex.regularizedHGFun a b z := by
  classical
  unfold genRegularizedHG
  split_ifs with h hF
  · rfl
  · exact False.elim (hF (genPrincipalContinuation_exists a b h))
  · rfl

/-- The regularized principal function is analytic on the cut plane for `p = q + 1`. -/
theorem analyticOnNhd_genRegularizedHG {a b : Multiset ℂ} (h : a.card = b.card + 1) :
    AnalyticOnNhd ℂ (genRegularizedHG a b) cutPlane := by
  have hF := genPrincipalContinuation_exists a b h
  have heq : genRegularizedHG a b = (Classical.choice hF).value :=
    funext (genRegularizedHG_eq_choice h hF)
  rw [heq]
  exact (Classical.choice hF).analytic

end DLMF.Hypergeometric

end
