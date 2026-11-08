/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Basic
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenReal
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenInterval
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenEndpoint
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenDominant
public import DLMFMathlib.Topology.Order.MonotoneUnbounded

/-!
# The Liouville–Green (WKBJ) approximation (DLMF §2.7(iii))

The Liouville–Green theorem for `w'' = (f + g) w` on an interval `(a₁, a₂)`, with error bounds
controlled by the variation of the error-control function
`F = ∫ (f^{-1/4} (f^{-1/4})'' - g f^{-1/2})`.

## Main results

* `liouvilleGreen_interval`: the theorem on a finite interval (DLMF 2.7.20–2.7.25).
* `liouvilleGreen_recessive_atTop`, `liouvilleGreen_recessive_isEquivalent`: the recessive
  solution for `a₂ = +∞` (DLMF 2.7.22–2.7.23, 2.7.27).
* `liouvilleGreen_interval_isEquivalent`, `liouvilleGreen_dominant`: the asymptotic forms at the
  endpoints (DLMF 2.7.26–2.7.30).
* `sqrt_add_log_expansion`, `liouvilleGreen_example`: the example `w'' = (x + ln x) w`
  (DLMF 2.7.31–2.7.34).

## Implementation notes

The integrand of `F` is DLMFMathlib's `LiouvilleGreen.errorDensity f f' f'' g` (with `f'`,
`f''` the derivatives of `f`), so `𝒱_{a₁,x}(F) = ∫_{(a₁,x]} |errorDensity|` (2.7.25). The case
`a₂ = +∞` is a corollary of `LiouvilleGreen.exists_solution_exp_of_pos` (Olver, Ch. 6,
Thm. 2.1) with `u = 1`.
-/

@[expose] public noncomputable section

open Set Filter Asymptotics MeasureTheory
open scoped Topology

namespace DLMF.AsymptoticApproximations

open LiouvilleGreen

/-- The recessive solution controlled from the right endpoint of a bounded interval. -/
private theorem exists_interval_recessive {a b : ℝ} (hab : a < b)
    {f f' f'' g ξ : ℝ → ℝ} (hd : IsLiouvilleGreenData f f' f'' g ξ (Ioo a b))
    (hV : ∀ x ∈ Ioo a b,
      IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ico x b)) :
    ∃ ε ε' : ℝ → ℝ, IsLiouvilleGreenSolutionOn f g
        (fun x => liouvilleGreenApproximant f ξ (-1) x * (1 + ε x)) (Ioo a b) ∧
      ∀ x ∈ Ioo a b, HasDerivAt ε (ε' x) x ∧
        |ε x| ≤ Real.exp ((∫ t in Ico x b, |errorDensity f f' f'' g t|) / 2) - 1 ∧
        (√(f x))⁻¹ * |ε' x| / 2 ≤
          Real.exp ((∫ t in Ico x b, |errorDensity f f' f'' g t|) / 2) - 1 := by
  obtain ⟨ε, ε', w', H⟩ := LiouvilleGreen.Interval.exists_solution_exp_of_pos hab one_pos
    hd.pos hd.hasDerivAt_f hd.hasDerivAt_f' hd.continuousOn_f'' hd.continuousOn_g
    hd.hasDerivAt_ξ (fun x hx => (hV x hx).mono_set Ioo_subset_Ico_self)
  refine ⟨ε, ε', ⟨w', fun x hx => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨-, h2, h3, -, -⟩ := H x hx
    refine ⟨?_, ?_⟩
    · convert h2 using 2 with y
      simp [liouvilleGreenApproximant]
    · convert h3 using 1
      simp [liouvilleGreenApproximant]
  · obtain ⟨h1, -, -, h4, h5⟩ := H x hx
    rw [← integral_Ico_eq_integral_Ioo] at h4 h5
    refine ⟨h1, by simpa using h4, ?_⟩
    have hs : 0 < √(f x) := Real.sqrt_pos.2 (hd.pos x hx)
    rw [mul_one] at h5
    rw [inv_mul_eq_div, div_div, div_le_iff₀ (by positivity)]
    calc |ε' x| ≤ 2 * √(f x) *
          (Real.exp ((∫ t in Ico x b, |errorDensity f f' f'' g t|) / 2) - 1) := h5
      _ = _ := by ring

/-- Reflection preserves the error density of a real Liouville–Green equation. -/
private theorem errorDensity_reflection (f f' f'' g : ℝ → ℝ) (x : ℝ) :
    errorDensity (fun t => f (-t)) (fun t => -f' (-t))
        (fun t => f'' (-t)) (fun t => g (-t)) x = errorDensity f f' f'' g (-x) := by
  simp [errorDensity]

/-- **The Liouville–Green approximation theorem** (DLMF 2.7.20–2.7.25) on a finite interval
`(a₁, a₂)`: if `f > 0` is `C²` and `g` continuous, then `w'' = (f + g) w` has `C²` solutions
`w₁ = f^{-1/4} e^{ξ} (1 + ε₁)` and `w₂ = f^{-1/4} e^{-ξ} (1 + ε₂)` with
`|ε_j(x)|, ½ f^{-1/2}(x) |ε_j'(x)| ≤ exp(½ 𝒱_{a_j,x}(F)) - 1`, provided the variations
`𝒱_{a₁,x}(F) = ∫_{a₁}^x |F'|` and `𝒱_{x,a₂}(F)` are finite (integrability hypotheses). -/
@[dlmf 2.7.E20, dlmf 2.7.E21, dlmf 2.7.E22, dlmf 2.7.E23, dlmf 2.7.E24, dlmf 2.7.E25]
theorem liouvilleGreen_interval {a₁ a₂ : ℝ} (ha : a₁ < a₂) {f f' f'' g ξ : ℝ → ℝ}
    (hd : IsLiouvilleGreenData f f' f'' g ξ (Ioo a₁ a₂)) :
    ((∀ x ∈ Ioo a₁ a₂, IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioc a₁ x)) →
      ∃ ε ε' : ℝ → ℝ, IsLiouvilleGreenSolutionOn f g
          (fun x => liouvilleGreenApproximant f ξ 1 x * (1 + ε x)) (Ioo a₁ a₂) ∧
        ∀ x ∈ Ioo a₁ a₂, HasDerivAt ε (ε' x) x ∧
          |ε x| ≤ Real.exp ((∫ t in Ioc a₁ x, |errorDensity f f' f'' g t|) / 2) - 1 ∧
          (√(f x))⁻¹ * |ε' x| / 2 ≤
            Real.exp ((∫ t in Ioc a₁ x, |errorDensity f f' f'' g t|) / 2) - 1) ∧
    ((∀ x ∈ Ioo a₁ a₂, IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ico x a₂)) →
      ∃ ε ε' : ℝ → ℝ, IsLiouvilleGreenSolutionOn f g
          (fun x => liouvilleGreenApproximant f ξ (-1) x * (1 + ε x)) (Ioo a₁ a₂) ∧
        ∀ x ∈ Ioo a₁ a₂, HasDerivAt ε (ε' x) x ∧
          |ε x| ≤ Real.exp ((∫ t in Ico x a₂, |errorDensity f f' f'' g t|) / 2) - 1 ∧
          (√(f x))⁻¹ * |ε' x| / 2 ≤
            Real.exp ((∫ t in Ico x a₂, |errorDensity f f' f'' g t|) / 2) - 1) := by
  have hneg : ∀ x ∈ Ioo (-a₂) (-a₁), -x ∈ Ioo a₁ a₂ := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hdR : IsLiouvilleGreenData (fun t => f (-t)) (fun t => -f' (-t))
      (fun t => f'' (-t)) (fun t => g (-t)) (fun t => -ξ (-t)) (Ioo (-a₂) (-a₁)) := by
    refine ⟨fun x hx => hd.pos (-x) (hneg x hx), ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simpa [Function.comp_def] using
        (hd.hasDerivAt_f (-x) (hneg x hx)).comp x (hasDerivAt_neg x)
    · intro x hx
      convert ((hd.hasDerivAt_f' (-x) (hneg x hx)).comp x (hasDerivAt_neg x)).neg using 1 <;>
        simp [Function.comp_def, funext_iff]
    · exact hd.continuousOn_f''.comp continuous_neg.continuousOn hneg
    · exact hd.continuousOn_g.comp continuous_neg.continuousOn hneg
    · intro x hx
      convert ((hd.hasDerivAt_ξ (-x) (hneg x hx)).comp x (hasDerivAt_neg x)).neg using 1 <;>
        simp [Function.comp_def, funext_iff]
  constructor
  · intro hV
    have hVR : ∀ c ∈ Ioo (-a₂) (-a₁), IntegrableOn
        (fun t => |errorDensity (fun t => f (-t)) (fun t => -f' (-t))
          (fun t => f'' (-t)) (fun t => g (-t)) t|) (Ico c (-a₁)) := by
      intro c hc
      rw [integrableOn_Ico_iff_integrableOn_Ioo]
      have hp : (fun t : ℝ => -t) ⁻¹' Ioo a₁ (-c) = Ioo c (-a₁) := by
        ext t
        simp only [mem_preimage, mem_Ioo]
        constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
      have hi := (MeasurePreserving.integrableOn_comp_preimage
        (Measure.measurePreserving_neg volume) (Homeomorph.neg ℝ).measurableEmbedding).2
          ((hV (-c) (hneg c hc)).mono_set Ioo_subset_Ioc_self)
      rw [hp] at hi
      simpa only [Function.comp_def, errorDensity_reflection] using hi
    obtain ⟨ε, ε', ⟨w', hw⟩, H⟩ := exists_interval_recessive (neg_lt_neg ha) hdR hVR
    have hVI : ∀ x ∈ Ioo a₁ a₂,
        (∫ t in Ico (-x) (-a₁), |errorDensity (fun t => f (-t)) (fun t => -f' (-t))
            (fun t => f'' (-t)) (fun t => g (-t)) t|) =
          ∫ t in Ioc a₁ x, |errorDensity f f' f'' g t| := by
      intro x hx
      rw [integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      have hp : (fun t : ℝ => -t) ⁻¹' Ioo a₁ x = Ioo (-x) (-a₁) := by
        ext t
        simp only [mem_preimage, mem_Ioo]
        constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
      simpa only [hp, errorDensity_reflection] using
        (Measure.measurePreserving_neg volume).setIntegral_preimage_emb
          (Homeomorph.neg ℝ).measurableEmbedding
          (fun t => |errorDensity f f' f'' g t|) (Ioo a₁ x)
    refine ⟨fun x => ε (-x), fun x => -ε' (-x), ⟨fun x => -w' (-x), ?_⟩, ?_⟩
    · intro x hx
      have hxR : -x ∈ Ioo (-a₂) (-a₁) := ⟨neg_lt_neg hx.2, neg_lt_neg hx.1⟩
      obtain ⟨h1, h2⟩ := hw (-x) hxR
      constructor
      · simpa [liouvilleGreenApproximant, Function.comp_def] using
          h1.comp x (hasDerivAt_neg x)
      · convert (h2.comp x (hasDerivAt_neg x)).neg using 1 <;>
          simp [liouvilleGreenApproximant, Function.comp_def, funext_iff]
    · intro x hx
      have hxR : -x ∈ Ioo (-a₂) (-a₁) := ⟨neg_lt_neg hx.2, neg_lt_neg hx.1⟩
      obtain ⟨h1, h2, h3⟩ := H (-x) hxR
      refine ⟨by simpa [Function.comp_def, Pi.neg_apply] using h1.comp x (hasDerivAt_neg x), ?_, ?_⟩
      · simpa only [neg_neg, hVI x hx] using h2
      · simpa only [neg_neg, abs_neg, hVI x hx] using h3
  · exact exists_interval_recessive ha hd

/-- DLMF 2.7.22–2.7.23 for the half-line `(a, ∞)` (`a₂ = +∞`, `j = 2`): the recessive solution
`w₂ = f^{-1/4} e^{-ξ} (1 + ε₂)` with `|ε₂|, ½ f^{-1/2} |ε₂'| ≤ exp(½ 𝒱_{x,∞}(F)) - 1`.
Corollary of DLMFMathlib's `LiouvilleGreen.exists_solution_exp_of_pos` with `u = 1`. -/
@[dlmf 2.7.E22, dlmf 2.7.E23, dlmf 2.7.E20]
theorem liouvilleGreen_recessive_atTop {a : ℝ} {f f' f'' g ξ : ℝ → ℝ}
    (hd : IsLiouvilleGreenData f f' f'' g ξ (Ioi a))
    (hV : ∀ c, a < c → IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioi c)) :
    ∃ ε ε' : ℝ → ℝ, IsLiouvilleGreenSolutionOn f g
        (fun x => liouvilleGreenApproximant f ξ (-1) x * (1 + ε x)) (Ioi a) ∧
      ∀ x ∈ Ioi a, HasDerivAt ε (ε' x) x ∧
        |ε x| ≤ Real.exp ((∫ t in Ioi x, |errorDensity f f' f'' g t|) / 2) - 1 ∧
        (√(f x))⁻¹ * |ε' x| / 2 ≤
          Real.exp ((∫ t in Ioi x, |errorDensity f f' f'' g t|) / 2) - 1 := by
  obtain ⟨ε, ε', w', H⟩ := exists_solution_exp_of_pos (a := a) one_pos (g := g)
    (fun x hx => hd.pos x hx) (fun x hx => hd.hasDerivAt_f x hx)
    (fun x hx => hd.hasDerivAt_f' x hx) hd.continuousOn_f'' hd.continuousOn_g
    (fun x hx => hd.hasDerivAt_ξ x hx) hV
  refine ⟨ε, ε', ⟨w', fun x hx => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨-, h2, h3, -, -⟩ := H x hx
    refine ⟨?_, ?_⟩
    · convert h2 using 2 with y
      simp [liouvilleGreenApproximant]
    · convert h3 using 1
      simp [liouvilleGreenApproximant]
  · obtain ⟨h1, -, -, h4, h5⟩ := H x hx
    refine ⟨h1, by simpa using h4, ?_⟩
    have hs : 0 < √(f x) := Real.sqrt_pos.2 (hd.pos x hx)
    rw [mul_one] at h5
    rw [inv_mul_eq_div, div_div, div_le_iff₀ (by positivity)]
    calc |ε' x| ≤ 2 * √(f x) * (Real.exp ((∫ t in Ioi x, |errorDensity f f' f'' g t|) / 2) - 1) :=
          h5
      _ = _ := by ring

/-- DLMF 2.7.27 for `a₂ = +∞`: `w₂(x) ∼ f^{-1/4}(x) exp(-∫ f^{1/2})` as `x → +∞`, for the
recessive solution of `liouvilleGreen_recessive_atTop`. -/
@[dlmf 2.7.E27]
theorem liouvilleGreen_recessive_isEquivalent {a : ℝ} {f f' f'' g ξ : ℝ → ℝ}
    (hd : IsLiouvilleGreenData f f' f'' g ξ (Ioi a))
    (hV : ∀ c, a < c → IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioi c)) :
    ∃ ε : ℝ → ℝ, IsLiouvilleGreenSolutionOn f g
        (fun x => liouvilleGreenApproximant f ξ (-1) x * (1 + ε x)) (Ioi a) ∧
      (fun x => liouvilleGreenApproximant f ξ (-1) x * (1 + ε x)) ~[atTop]
          liouvilleGreenApproximant f ξ (-1) := by
  obtain ⟨ε, ε', hsol, H⟩ := liouvilleGreen_recessive_atTop hd hV
  refine ⟨ε, hsol, ?_⟩
  have hε : Tendsto ε atTop (𝓝 0) := by
    have hb := tendsto_exp_integral_Ioi_sub_one (hV (a + 1) (by linarith)) (1 / 2)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_gt_atTop a] with x hx
    rw [Real.norm_eq_abs, show 1 / 2 * ∫ t in Ioi x, |errorDensity f f' f'' g t| =
      (∫ t in Ioi x, |errorDensity f f' f'' g t|) / 2 by ring]
    exact (H x hx).2.1
  refine isEquivalent_of_tendsto_one ?_
  have h1 : Tendsto (fun x => 1 + ε x) atTop (𝓝 1) := by simpa using hε.const_add 1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop a] with x hx
  have hne : liouvilleGreenApproximant f ξ (-1) x ≠ 0 := by
    unfold liouvilleGreenApproximant
    exact mul_ne_zero (Real.rpow_pos_of_pos (hd.pos x hx) _).ne' (Real.exp_pos _).ne'
  simp only [Pi.div_apply]
  field_simp

/-- A relative error tending to zero gives the stated Liouville–Green equivalence. -/
private theorem isEquivalent_approximant_mul_one_add {l : Filter ℝ}
    {f ξ ε : ℝ → ℝ} {σ : ℝ} (hf : ∀ᶠ x in l, 0 < f x) (hε : Tendsto ε l (𝓝 0)) :
    (fun x => liouvilleGreenApproximant f ξ σ x * (1 + ε x)) ~[l]
      liouvilleGreenApproximant f ξ σ := by
  refine isEquivalent_of_tendsto_one ?_
  have h1 : Tendsto (fun x => 1 + ε x) l (𝓝 1) := by simpa using hε.const_add 1
  refine h1.congr' ?_
  filter_upwards [hf] with x hx
  have hne : liouvilleGreenApproximant f ξ σ x ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos hx _).ne' (Real.exp_pos _).ne'
  simp only [Pi.div_apply]
  field_simp

/-- A solution with a recessive Liouville–Green leading term is nonzero eventually and small
relative to the amplitude. -/
private theorem recessive_normalization {l : Filter ℝ} {f ξ w : ℝ → ℝ} {σ : ℝ}
    (hf : ∀ᶠ x in l, 0 < f x) (hw : w ~[l] liouvilleGreenApproximant f ξ σ)
    (hE : Tendsto (fun x => Real.exp (σ * ξ x)) l (𝓝 0)) :
    (∀ᶠ x in l, w x ≠ 0) ∧
      Tendsto (fun x => w x / f x ^ (-(1 / 4) : ℝ)) l (𝓝 0) := by
  have hp : ∀ᶠ x in l, 0 < liouvilleGreenApproximant f ξ σ x := hf.mono fun x hx =>
    mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)
  refine ⟨(hw.eventually_pos hp).mono fun _ hx => hx.ne', ?_⟩
  have hr := (isEquivalent_iff_tendsto_one (hp.mono fun _ hx => hx.ne')).1 hw
  have ht : Tendsto (fun x => w x / liouvilleGreenApproximant f ξ σ x *
      Real.exp (σ * ξ x)) l (𝓝 0) := by simpa using hr.mul hE
  refine ht.congr' ?_
  filter_upwards [hf] with x hx
  have hA := (Real.rpow_pos_of_pos hx (-(1 / 4) : ℝ)).ne'
  have hExp := (Real.exp_pos (σ * ξ x)).ne'
  simp only [liouvilleGreenApproximant]
  field_simp

/-- The phase increases throughout a Liouville–Green interval. -/
private theorem monotoneOn_phase {a b : ℝ} {f f' f'' g ξ : ℝ → ℝ}
    (hd : IsLiouvilleGreenData f f' f'' g ξ (Ioo a b)) : MonotoneOn ξ (Ioo a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioo a b)
    (fun x hx => (hd.hasDerivAt_ξ x hx).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Ioo] at hx
      exact (hd.hasDerivAt_ξ x hx).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
  rw [interior_Ioo] at hx
  rw [(hd.hasDerivAt_ξ x hx).deriv]
  exact Real.sqrt_nonneg _

/-- DLMF 2.7.26–2.7.27, with the singular-endpoint condition from the following paragraph:
if the error-control variation is finite and `|ξ|` is unbounded at both endpoints, there are
unique recessive solutions equivalent to `f^{-1/4} e^{ξ}` at `a₁+` and to `f^{-1/4} e^{-ξ}` at
`a₂-`. The endpoint condition is essential: at a regular endpoint asymptotic equivalence
alone does not determine a solution. -/
@[dlmf 2.7.E26, dlmf 2.7.E27]
theorem liouvilleGreen_interval_isEquivalent {a₁ a₂ : ℝ} (ha : a₁ < a₂) {f f' f'' g ξ : ℝ → ℝ}
    (hd : IsLiouvilleGreenData f f' f'' g ξ (Ioo a₁ a₂))
    (hV : IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioo a₁ a₂))
    (hξ₁ : ¬ IsBoundedUnder (· ≤ ·) (𝓝[>] a₁) (fun x => |ξ x|))
    (hξ₂ : ¬ IsBoundedUnder (· ≤ ·) (𝓝[<] a₂) (fun x => |ξ x|)) :
    (∃ w₁ : ℝ → ℝ, IsLiouvilleGreenSolutionOn f g w₁ (Ioo a₁ a₂) ∧
        w₁ ~[𝓝[>] a₁] liouvilleGreenApproximant f ξ 1 ∧
      ∀ v, IsLiouvilleGreenSolutionOn f g v (Ioo a₁ a₂) →
          v ~[𝓝[>] a₁] liouvilleGreenApproximant f ξ 1 →
        EqOn v w₁ (Ioo a₁ a₂)) ∧
    (∃ w₂ : ℝ → ℝ, IsLiouvilleGreenSolutionOn f g w₂ (Ioo a₁ a₂) ∧
        w₂ ~[𝓝[<] a₂] liouvilleGreenApproximant f ξ (-1) ∧
      ∀ v, IsLiouvilleGreenSolutionOn f g v (Ioo a₁ a₂) →
          v ~[𝓝[<] a₂] liouvilleGreenApproximant f ξ (-1) →
        EqOn v w₂ (Ioo a₁ a₂)) := by
  have hV₁ : ∀ x ∈ Ioo a₁ a₂,
      IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioc a₁ x) :=
    fun x hx => hV.mono_set fun t ht => ⟨ht.1, ht.2.trans_lt hx.2⟩
  have hV₂ : ∀ x ∈ Ioo a₁ a₂,
      IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ico x a₂) :=
    fun x hx => hV.mono_set fun t ht => ⟨hx.1.trans_le ht.1, ht.2⟩
  obtain ⟨ε₁, ε₁', hw₁, H₁⟩ := (liouvilleGreen_interval ha hd).1 hV₁
  obtain ⟨ε₂, ε₂', hw₂, H₂⟩ := (liouvilleGreen_interval ha hd).2 hV₂
  have htail := LiouvilleGreen.IntervalVolterra.tendsto_integral_Ioo ha hV
  have hhead : Tendsto (fun x => ∫ t in Ioc a₁ x, |errorDensity f f' f'' g t|)
      (𝓝[>] a₁) (𝓝 0) := by
    have hi : IntegrableOn (fun t => |errorDensity f f' f'' g t|) (uIcc a₁ a₂) := by
      rw [uIcc_of_le ha.le, integrableOn_Icc_iff_integrableOn_Ioo]
      exact hV
    have hc := intervalIntegral.continuousOn_primitive_interval hi
    rw [uIcc_of_le ha.le] at hc
    have ht : ContinuousWithinAt
        (fun x => ∫ t in a₁..x, |errorDensity f f' f'' g t|) (Ioi a₁) a₁ :=
      (hc a₁ ⟨le_rfl, ha.le⟩).mono_of_mem_nhdsWithin (by
        exact mem_nhdsWithin.2
          ⟨Iio a₂, isOpen_Iio, ha, fun x hx => ⟨hx.2.le, hx.1.le⟩⟩)
    have ht' : Tendsto (fun x => ∫ t in a₁..x, |errorDensity f f' f'' g t|)
        (𝓝[>] a₁) (𝓝 0) := by simpa using ht.tendsto
    refine ht'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact intervalIntegral.integral_of_le hx.le
  have hε₁ : Tendsto ε₁ (𝓝[>] a₁) (𝓝 0) := by
    have hb : Tendsto (fun x => Real.exp
        ((∫ t in Ioc a₁ x, |errorDensity f f' f'' g t|) / 2) - 1)
        (𝓝[>] a₁) (𝓝 0) := by
      simpa using ((Real.continuous_exp.tendsto 0).comp
        (by simpa using hhead.div_const 2)).sub_const 1
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [Ioo_mem_nhdsGT ha] with x hx
    simpa only [Real.norm_eq_abs] using (H₁ x hx).2.1
  have hε₂ : Tendsto ε₂ (𝓝[<] a₂) (𝓝 0) := by
    have hb : Tendsto (fun x => Real.exp
        ((∫ t in Ioo x a₂, |errorDensity f f' f'' g t|) / 2) - 1)
        (𝓝[<] a₂) (𝓝 0) := by
      simpa using ((Real.continuous_exp.tendsto 0).comp
        (by simpa using htail.div_const 2)).sub_const 1
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [Ioo_mem_nhdsLT ha] with x hx
    simpa only [Real.norm_eq_abs, integral_Ico_eq_integral_Ioo] using (H₂ x hx).2.1
  have hf₁ : ∀ᶠ x in 𝓝[>] a₁, 0 < f x :=
    (show ∀ᶠ x in 𝓝[>] a₁, x ∈ Ioo a₁ a₂ from Ioo_mem_nhdsGT ha).mono
      fun x hx => hd.pos x hx
  have hf₂ : ∀ᶠ x in 𝓝[<] a₂, 0 < f x :=
    (show ∀ᶠ x in 𝓝[<] a₂, x ∈ Ioo a₁ a₂ from Ioo_mem_nhdsLT ha).mono
      fun x hx => hd.pos x hx
  have he₁ := isEquivalent_approximant_mul_one_add (ξ := ξ) (σ := 1) hf₁ hε₁
  have he₂ := isEquivalent_approximant_mul_one_add (ξ := ξ) (σ := -1) hf₂ hε₂
  have hξbot := (monotoneOn_phase hd).tendsto_atBot_nhdsGT_of_not_isBoundedUnder_abs ha hξ₁
  have hξtop := (monotoneOn_phase hd).tendsto_atTop_nhdsLT_of_not_isBoundedUnder_abs ha hξ₂
  have hnorm₁ := recessive_normalization hf₁ he₁ (by
    simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp hξbot)
  have hnorm₂ := recessive_normalization hf₂ he₂ (by
    simpa [Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hξtop)
  have hA : ∀ x ∈ Ioo a₁ a₂, 0 < f x ^ (-(1 / 4) : ℝ) :=
    fun x hx => Real.rpow_pos_of_pos (hd.pos x hx) _
  have hξA : ∀ x ∈ Ioo a₁ a₂,
      HasDerivAt ξ (((f x ^ (-(1 / 4) : ℝ)) ^ 2)⁻¹) x := by
    intro x hx
    rw [(LiouvilleGreen.Interval.amplitude (g := g) hd.pos hd.hasDerivAt_f hd.hasDerivAt_f'
      hd.continuousOn_f'' hx).2.2.2.2.1]
    exact hd.hasDerivAt_ξ x hx
  have hfc : ContinuousOn f (Ioo a₁ a₂) :=
    fun x hx => (hd.hasDerivAt_f x hx).continuousAt.continuousWithinAt
  have hq : ContinuousOn (fun x => f x + g x) (Ioo a₁ a₂) := hfc.add hd.continuousOn_g
  constructor
  · refine ⟨_, hw₁, he₁, ?_⟩
    intro v hv hve
    obtain ⟨u', hu⟩ := hw₁
    obtain ⟨v', hv⟩ := hv
    exact LiouvilleGreen.Interval.eqOn_of_recessive_ratio_left ha hA hξA hξbot hq
      (fun x hx => (hu x hx).1) (fun x hx => (hu x hx).2)
      (fun x hx => (hv x hx).1) (fun x hx => (hv x hx).2)
      hnorm₁.1 hnorm₁.2 ((isEquivalent_iff_tendsto_one hnorm₁.1).1 (hve.trans he₁.symm))
  · refine ⟨_, hw₂, he₂, ?_⟩
    intro v hv hve
    obtain ⟨u', hu⟩ := hw₂
    obtain ⟨v', hv⟩ := hv
    exact LiouvilleGreen.Interval.eqOn_of_recessive_ratio ha hA hξA hξtop hq
      (fun x hx => (hu x hx).1) (fun x hx => (hu x hx).2)
      (fun x hx => (hv x hx).1) (fun x hx => (hv x hx).2)
      hnorm₂.1 hnorm₂.2 ((isEquivalent_iff_tendsto_one hnorm₂.1).1 (hve.trans he₂.symm))

/-- DLMF 2.7.28–2.7.30: if in addition `|ξ|` is unbounded as `x → a₁+` and as `x → a₂-`, there
are solutions `w₃ ∼ f^{-1/4} e^{ξ}` as `x → a₂-` and `w₄ ∼ f^{-1/4} e^{-ξ}` as `x → a₁+`, and
`w₁/w₄ → 0` as `x → a₁+` (`w₁` recessive, `w₄` dominant), `w₂/w₃ → 0` as `x → a₂-`. -/
@[dlmf 2.7.E28, dlmf 2.7.E29, dlmf 2.7.E30, dlmf 2.7.iii]
theorem liouvilleGreen_dominant {a₁ a₂ : ℝ} (ha : a₁ < a₂) {f f' f'' g ξ : ℝ → ℝ}
    (hd : IsLiouvilleGreenData f f' f'' g ξ (Ioo a₁ a₂))
    (hV : IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioo a₁ a₂))
    (hξ₁ : ¬ IsBoundedUnder (· ≤ ·) (𝓝[>] a₁) (fun x => |ξ x|))
    (hξ₂ : ¬ IsBoundedUnder (· ≤ ·) (𝓝[<] a₂) (fun x => |ξ x|))
    {w₁ w₂ : ℝ → ℝ} (hw₁ : IsLiouvilleGreenSolutionOn f g w₁ (Ioo a₁ a₂))
        (hw₂ : IsLiouvilleGreenSolutionOn f g w₂ (Ioo a₁ a₂))
    (hw₁e : w₁ ~[𝓝[>] a₁] liouvilleGreenApproximant f ξ 1)
        (hw₂e : w₂ ~[𝓝[<] a₂] liouvilleGreenApproximant f ξ (-1)) :
    ∃ w₃ w₄ : ℝ → ℝ, IsLiouvilleGreenSolutionOn f g w₃ (Ioo a₁ a₂) ∧
        IsLiouvilleGreenSolutionOn f g w₄ (Ioo a₁ a₂) ∧
      w₃ ~[𝓝[<] a₂] liouvilleGreenApproximant f ξ 1 ∧
          w₄ ~[𝓝[>] a₁] liouvilleGreenApproximant f ξ (-1) ∧
      Tendsto (fun x => w₁ x / w₄ x) (𝓝[>] a₁) (𝓝 0) ∧
      Tendsto (fun x => w₂ x / w₃ x) (𝓝[<] a₂) (𝓝 0) := by
  clear hV
  have hA : ∀ x ∈ Ioo a₁ a₂, 0 < f x ^ (-(1 / 4) : ℝ) :=
    fun x hx => Real.rpow_pos_of_pos (hd.pos x hx) _
  have hξA : ∀ x ∈ Ioo a₁ a₂,
      HasDerivAt ξ (((f x ^ (-(1 / 4) : ℝ)) ^ 2)⁻¹) x := by
    intro x hx
    rw [(LiouvilleGreen.Interval.amplitude (g := g) hd.pos hd.hasDerivAt_f hd.hasDerivAt_f'
      hd.continuousOn_f'' hx).2.2.2.2.1]
    exact hd.hasDerivAt_ξ x hx
  have hξbot := (monotoneOn_phase hd).tendsto_atBot_nhdsGT_of_not_isBoundedUnder_abs ha hξ₁
  have hξtop := (monotoneOn_phase hd).tendsto_atTop_nhdsLT_of_not_isBoundedUnder_abs ha hξ₂
  have hfc : ContinuousOn f (Ioo a₁ a₂) :=
    fun x hx => (hd.hasDerivAt_f x hx).continuousAt.continuousWithinAt
  have hq : ContinuousOn (fun x => f x + g x) (Ioo a₁ a₂) := hfc.add hd.continuousOn_g
  have hE₁ : ∀ᶠ x in 𝓝[>] a₁, liouvilleGreenApproximant f ξ 1 x ≠ 0 := by
    filter_upwards [Ioo_mem_nhdsGT ha] with x hx
    exact (mul_pos (hA x hx) (Real.exp_pos _)).ne'
  have hE₂ : ∀ᶠ x in 𝓝[<] a₂, liouvilleGreenApproximant f ξ (-1) x ≠ 0 := by
    filter_upwards [Ioo_mem_nhdsLT ha] with x hx
    exact (mul_pos (hA x hx) (Real.exp_pos _)).ne'
  have hnorm₁ : Tendsto (fun x => w₁ x / (f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x)))
      (𝓝[>] a₁) (𝓝 1) := by
    convert (isEquivalent_iff_tendsto_one hE₁).1 hw₁e using 1
    ext x
    simp [liouvilleGreenApproximant]
  have hnorm₂ : Tendsto (fun x => w₂ x / (f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x)))
      (𝓝[<] a₂) (𝓝 1) := by
    convert (isEquivalent_iff_tendsto_one hE₂).1 hw₂e using 1
    ext x
    simp [liouvilleGreenApproximant]
  obtain ⟨u₁', hu₁⟩ := hw₁
  obtain ⟨u₂', hu₂⟩ := hw₂
  obtain ⟨w₃, w₃', hw₃, he₃, hr₂⟩ := LiouvilleGreen.Interval.exists_dominant_of_recessive
    ha hA hξA hξtop hq (fun x hx => (hu₂ x hx).1) (fun x hx => (hu₂ x hx).2) hnorm₂
  obtain ⟨w₄, w₄', hw₄, he₄, hr₁⟩ :=
    LiouvilleGreen.Interval.exists_dominant_of_recessive_left ha hA hξA hξbot hq
      (fun x hx => (hu₁ x hx).1) (fun x hx => (hu₁ x hx).2) hnorm₁
  refine ⟨w₃, w₄, ⟨w₃', hw₃⟩, ⟨w₄', hw₄⟩, ?_, ?_, hr₁, hr₂⟩
  · apply isEquivalent_of_tendsto_one
    convert he₃ using 1
    ext x
    simp [liouvilleGreenApproximant]
  · apply isEquivalent_of_tendsto_one
    convert he₄ using 1
    ext x
    simp [liouvilleGreenApproximant]

/-- DLMF 2.7.32: `(x + ln x)^{1/2} = x^{1/2} + ½ x^{-1/2} ln x + O(x^{-3/2} (ln x)²)` as
`x → +∞`. -/
@[dlmf 2.7.E32]
theorem sqrt_add_log_expansion :
    (fun x : ℝ => √(x + Real.log x) - (√x + Real.log x / (2 * √x)))
      =O[atTop] (fun x : ℝ => x ^ (-(3 / 2) : ℝ) * Real.log x ^ 2) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  let a := Real.sqrt (x + Real.log x)
  let b := Real.sqrt x
  have hb : 0 < b := Real.sqrt_pos.mpr hx0
  have ha : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  have hb2 : b ^ 2 = x := Real.sq_sqrt hx0.le
  have ha2 : a ^ 2 = x + Real.log x := Real.sq_sqrt (by linarith)
  have hsum : a + b ≠ 0 := by linarith
  have hlog : Real.log x = a ^ 2 - b ^ 2 := by linarith
  have herr : a - (b + Real.log x / (2 * b)) =
      -(Real.log x ^ 2 / (2 * b * (a + b) ^ 2)) := by
    rw [hlog]
    field_simp
    ring
  have hd : 0 < 2 * b * (a + b) ^ 2 := by positivity
  have hden : x * b ≤ 2 * b * (a + b) ^ 2 := by
    have hs : x ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg a]
    nlinarith
  have hp : x ^ (-(3 / 2) : ℝ) = 1 / (x * b) := by
    rw [Real.rpow_neg hx0.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hx0, Real.rpow_one, ← Real.sqrt_eq_rpow]
    simp only [one_div, b]
  change ‖a - (b + Real.log x / (2 * b))‖ ≤ _
  rw [herr, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), hp]
  calc Real.log x ^ 2 / (2 * b * (a + b) ^ 2) ≤ Real.log x ^ 2 / (x * b) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
    _ = 1 / (x * b) * Real.log x ^ 2 := by ring

/-- DLMF 2.7.31, 2.7.33–2.7.34 (example): the equation `w'' = (x + ln x) w` on `(0, ∞)` has a
recessive solution `w₂(x) ∼ x^{-1/4-√x} exp(2x^{1/2} - (2/3)x^{3/2})` and a dominant solution
`w₃(x) ∼ x^{-1/4+√x} exp((2/3)x^{3/2} - 2x^{1/2})` as `x → +∞`. -/
@[dlmf 2.7.E31, dlmf 2.7.E33, dlmf 2.7.E34]
theorem liouvilleGreen_example :
    ∃ w₂ w₃ : ℝ → ℝ,
      IsLiouvilleGreenSolutionOn (fun x => x + Real.log x) (fun _ => 0) w₂ (Ioi 0) ∧
      IsLiouvilleGreenSolutionOn (fun x => x + Real.log x) (fun _ => 0) w₃ (Ioi 0) ∧
      w₂ ~[atTop] (fun x => x ^ (-(1 / 4) - √x) *
        Real.exp (2 * x ^ (1 / 2 : ℝ) - 2 / 3 * x ^ (3 / 2 : ℝ))) ∧
      w₃ ~[atTop] (fun x => x ^ (-(1 / 4) + √x) *
        Real.exp (2 / 3 * x ^ (3 / 2 : ℝ) - 2 * x ^ (1 / 2 : ℝ))) := by
  sorry

end DLMF.AsymptoticApproximations
