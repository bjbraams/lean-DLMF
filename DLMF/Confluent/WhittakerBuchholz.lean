/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.Buchholz
public import DLMF.Confluent.Whittaker
public import DLMF.Confluent.Continuation
public import DLMF.Bessel.NeumannSeries
public import Mathlib.Analysis.Complex.TaylorSeries
public import DLMFMathlib.Analysis.Complex.TaylorParameter
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The Whittaker–Buchholz expansion (DLMF §13.24)

The Buchholz generating function defines the coefficients of Whittaker's expansion in Bessel
functions. Cauchy bounds control the coefficient series, and a differential recurrence relates
the coefficients to the normalized Whittaker equation.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Real Topology Nat
open DLMF.Hypergeometric DLMF.Bessel

namespace DLMF.Confluent

/-- `sinh t / t`, extended by `1` at the origin, stays within distance `sinh 1 - 1 < 1` of `1`
on the unit disc. -/
theorem norm_dslope_sinh_sub_one_le {t : ℂ} (ht : ‖t‖ ≤ 1) :
    ‖dslope sinh 0 t - 1‖ ≤ Real.sinh 1 - 1 := by
  have hreal : HasSum (fun n : ℕ => (1 : ℝ) / ((2 * (n + 1) + 1)! : ℝ)) (Real.sinh 1 - 1) := by
    have h := Real.hasSum_sinh 1
    simp only [one_pow] at h
    have := (hasSum_nat_add_iff' 1).mpr h
    simpa using this
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [dslope_same, (Complex.hasDerivAt_sinh 0).deriv, Complex.cosh_zero, sub_self, norm_zero]
    exact hreal.nonneg fun n => by positivity
  · have hs := (Complex.hasSum_sinh t).div_const t
    have hs' : HasSum (fun n : ℕ => t ^ (2 * n) / ((2 * n + 1)! : ℂ)) (dslope sinh 0 t) := by
      rw [dslope_of_ne _ ht0, slope_def_field, Complex.sinh_zero, sub_zero, sub_zero]
      refine hs.congr_fun fun n => ?_
      rw [pow_succ]; field_simp
    have h1 := (hasSum_nat_add_iff' 1).mpr hs'
    simp only [Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, zero_add,
      Nat.factorial_one, Nat.cast_one, div_one] at h1
    refine h1.norm_le_of_bounded hreal fun n => ?_
    rw [norm_div, norm_pow, Complex.norm_natCast]
    gcongr
    exact pow_le_one₀ (norm_nonneg _) ht

/-- `sinh 1 < 2`. -/
theorem real_sinh_one_lt_two : Real.sinh 1 < 2 := by
  rw [Real.sinh_eq]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_pos (-1)
  linarith

/-- The function `t/sinh t`, extended by `1` at `t = 0`. -/
private noncomputable def whittakerBesselBase (t : ℂ) : ℂ := if t=0 then 1 else t/sinh t

/-- On the unit disc, `coth t - 1/t` and `t/sinh t` are holomorphic and `t/sinh t` lies in the slit
plane. -/
private lemma whittakerBessel_core_analytic :
    DifferentiableOn ℂ (fun t : ℂ => cosh t/sinh t-t⁻¹) (Metric.ball 0 1) ∧
    DifferentiableOn ℂ whittakerBesselBase (Metric.ball 0 1) ∧
    ∀ t : ℂ, ‖t‖ < 1 → whittakerBesselBase t ∈ slitPlane := by
  set S : ℂ → ℂ := dslope sinh 0 with hS
  set h : ℂ → ℂ := fun t => t * cosh t - sinh t with hh
  set E : ℂ → ℂ := dslope (dslope h 0) 0 with hE
  have hhd : Differentiable ℂ h := by
    simp only [hh]; fun_prop
  have hSd : Differentiable ℂ S := fun x =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).mpr
      Complex.differentiable_sinh.differentiableOn x (Set.mem_univ x)).differentiableAt
      Filter.univ_mem
  have hE1 : Differentiable ℂ (dslope h 0) := fun x =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hhd.differentiableOn x
      (Set.mem_univ x)).differentiableAt Filter.univ_mem
  have hEd : Differentiable ℂ E := fun x =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hE1.differentiableOn x
      (Set.mem_univ x)).differentiableAt Filter.univ_mem
  have hS_ne : ∀ x : ℂ, x ≠ 0 → S x = sinh x / x := fun x hx => by
    rw [hS, dslope_of_ne _ hx, slope_def_field, Complex.sinh_zero, sub_zero, sub_zero]
  have hS0 : S 0 = 1 := by
    rw [hS, dslope_same, (Complex.hasDerivAt_sinh 0).deriv, Complex.cosh_zero]
  have hh0 : h 0 = 0 := by simp [hh]
  have hh'0 : deriv h 0 = 0 := by
    have hd : HasDerivAt h (1 * cosh 0 + 0 * sinh 0 - cosh 0) 0 :=
      ((hasDerivAt_id 0).mul (Complex.hasDerivAt_cosh 0)).sub (Complex.hasDerivAt_sinh 0)
    rw [hd.deriv]; ring
  have hE_ne : ∀ x : ℂ, x ≠ 0 → E x = h x / x ^ 2 := fun x hx => by
    rw [hE, dslope_of_ne _ hx, slope_def_field, dslope_same, hh'0, dslope_of_ne _ hx,
      slope_def_field, hh0]
    field_simp
    ring
  have hE0 : E 0 = 0 := by
    have hodd : ∀ x : ℂ, x ≠ 0 → E (-x) = -E x := fun x hx => by
      rw [hE_ne x hx, hE_ne (-x) (neg_ne_zero.mpr hx)]
      simp only [hh, Complex.cosh_neg, Complex.sinh_neg]
      ring
    have h1 : Tendsto E (𝓝[≠] 0) (𝓝 (E 0)) := (hEd 0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have h2 : Tendsto (fun x => E (-x)) (𝓝[≠] 0) (𝓝 (E 0)) := by
      have hn : Tendsto (fun x : ℂ => -x) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_neg.tendsto (0 : ℂ))
      exact ((hEd 0).continuousAt.tendsto.comp hn).mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun x => E (-x)) (𝓝[≠] 0) (𝓝 (-E 0)) := by
      refine h1.neg.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hodd x hx).symm
    have := tendsto_nhds_unique h2 h3
    linear_combination this / 2
  have hSb : ∀ x : ℂ, ‖x‖ < 1 → ‖S x - 1‖ < 1 := fun x hx =>
    (norm_dslope_sinh_sub_one_le hx.le).trans_lt (by linarith [real_sinh_one_lt_two])
  have hSre : ∀ x : ℂ, ‖x‖ < 1 → 0 < (S x).re := fun x hx => by
    have h1 := hSb x hx
    have h2 := Complex.abs_re_le_norm (S x - 1)
    rw [Complex.sub_re, Complex.one_re] at h2
    linarith [abs_le.mp (h2.trans h1.le), neg_abs_le ((S x).re - 1)]
  have hSne : ∀ x : ℂ, ‖x‖ < 1 → S x ≠ 0 := fun x hx h0 => by
    have := hSre x hx; rw [h0, Complex.zero_re] at this; exact lt_irrefl _ this
  have hslit : ∀ x : ℂ, ‖x‖ < 1 → 1 / S x ∈ slitPlane := fun x hx => by
    rw [mem_slitPlane_iff, one_div, Complex.inv_re]
    exact Or.inl (div_pos (hSre x hx) (Complex.normSq_pos.mpr (hSne x hx)))
  have hball : ∀ x ∈ Metric.ball (0 : ℂ) 1, ‖x‖ < 1 := fun x hx => by simpa using hx

  have hAeq : Set.EqOn (fun t : ℂ => cosh t/sinh t-t⁻¹)
      (fun t => E t/S t) (Metric.ball 0 1) := by
    intro t ht
    have ht' := hball t ht
    change cosh t/sinh t-t⁻¹=E t/S t
    rcases eq_or_ne t 0 with rfl | ht0
    · simp [hE0,hS0]
    · rw [hE_ne t ht0,hS_ne t ht0]
      have hsh : sinh t ≠ 0 := fun h0 => hSne t ht' (by rw [hS_ne t ht0,h0,zero_div])
      simp only [hh]
      field_simp
  have hBeq : Set.EqOn whittakerBesselBase (fun t => 1/S t) (Metric.ball 0 1) := by
    intro t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · simp [whittakerBesselBase,hS0]
    · simp only [whittakerBesselBase,ht0,↓reduceIte,hS_ne t ht0]
      field_simp
  have hAd : DifferentiableOn ℂ (fun t => E t/S t) (Metric.ball 0 1) :=
    fun t ht => ((hEd t).div (hSd t) (hSne t (hball t ht))).differentiableWithinAt
  have hBd : DifferentiableOn ℂ (fun t => 1/S t) (Metric.ball 0 1) :=
    fun t ht => ((differentiableAt_const _).div (hSd t)
      (hSne t (hball t ht))).differentiableWithinAt
  refine ⟨hAd.congr hAeq,hBd.congr hBeq,?_⟩
  intro t ht
  rw [hBeq (by simpa using ht)]
  exact hslit t ht

/-- The generating function of DLMF 13.24.3 is `exp(-(z/2)(coth t - 1/t)) (t/sinh t)^{1-2μ}`. -/
private lemma whittakerBesselGenerating_eq_core (μ z t : ℂ) :
    whittakerBesselGenerating μ z t=
      exp (-z/2*(cosh t/sinh t-t⁻¹))*whittakerBesselBase t^(1-2*μ) := by
  by_cases ht : t=0
  · simp [whittakerBesselGenerating,whittakerBesselBase,ht]
  · simp [whittakerBesselGenerating,whittakerBesselBase,ht]

/-- The generating function of DLMF 13.24.3 is holomorphic in `t` on the unit disc. -/
theorem whittakerBesselGenerating_differentiableOn (μ z : ℂ) :
    DifferentiableOn ℂ (whittakerBesselGenerating μ z) (Metric.ball 0 1) := by
  have h := whittakerBessel_core_analytic
  have hf : DifferentiableOn ℂ (fun t : ℂ =>
      exp (-z/2*(cosh t/sinh t-t⁻¹))*whittakerBesselBase t^(1-2*μ)) (Metric.ball 0 1) := by
    intro t ht
    have hA := h.1.differentiableAt (Metric.isOpen_ball.mem_nhds ht)
    have hB := h.2.1.differentiableAt (Metric.isOpen_ball.mem_nhds ht)
    exact (((hA.const_mul _).cexp).mul (hB.cpow (differentiableAt_const _)
      (h.2.2 t (by simpa using ht)))).differentiableWithinAt
  exact hf.congr fun t _ => whittakerBesselGenerating_eq_core μ z t

/-- The generating function of DLMF 13.24.3 is jointly continuous in `(z, t)` for `|t| < 1`. -/
theorem whittakerBesselGenerating_joint_continuousAt (μ : ℂ) {z t : ℂ} (ht : ‖t‖ < 1) :
    ContinuousAt (fun p : ℂ × ℂ => whittakerBesselGenerating μ p.1 p.2) (z,t) := by
  have ht' : t ∈ Metric.ball (0:ℂ) 1 := by simpa using ht
  have h := whittakerBessel_core_analytic
  have hA : ContinuousAt (fun p : ℂ × ℂ => cosh p.2/sinh p.2-p.2⁻¹) (z,t) :=
    (h.1.differentiableAt (Metric.isOpen_ball.mem_nhds ht')).continuousAt.comp (x:=(z,t)) continuousAt_snd
  have hBc : ContinuousAt whittakerBesselBase t :=
    (h.2.1.differentiableAt (Metric.isOpen_ball.mem_nhds ht')).continuousAt
  have hB : ContinuousAt (fun p : ℂ × ℂ => whittakerBesselBase p.2) (z,t) :=
    hBc.comp (g:=whittakerBesselBase) (f:=fun p : ℂ × ℂ => p.2) (x:=(z,t)) continuousAt_snd
  have hf : ContinuousAt (fun p : ℂ × ℂ =>
      exp (-p.1/2*(cosh p.2/sinh p.2-p.2⁻¹))*whittakerBesselBase p.2^(1-2*μ)) (z,t) :=
    (((continuousAt_fst.neg.div_const 2).mul hA).cexp).mul
      (hB.cpow continuousAt_const (h.2.2 t ht))
  exact hf.congr (Eventually.of_forall fun p => (whittakerBesselGenerating_eq_core μ p.1 p.2).symm)

/-- For `0 < |t| < 1`, `t/sinh t` lies in the slit plane. -/
private lemma whittakerBessel_base_mem_slit {t : ℂ} (ht : t ≠ 0) (hsmall : ‖t‖ < 1) :
    t/sinh t ∈ slitPlane := by
  have hbd := (norm_dslope_sinh_sub_one_le hsmall.le).trans_lt
    (show Real.sinh 1-1 < 1 by linarith [real_sinh_one_lt_two])
  have h1 := Complex.abs_re_le_norm (dslope sinh 0 t-1)
  rw [Complex.sub_re,Complex.one_re] at h1
  have hS : 0 < (dslope sinh 0 t).re := by linarith [neg_abs_le ((dslope sinh 0 t).re-1)]
  have hSn : dslope sinh 0 t ≠ 0 := fun h0 => by simp [h0] at hS
  have hEq : dslope sinh 0 t=sinh t/t := by
    rw [dslope_of_ne _ ht,slope_def_field,sinh_zero,sub_zero,sub_zero]
  have hBase : t/sinh t=(dslope sinh 0 t)⁻¹ := by rw [hEq,inv_div]
  rw [hBase,mem_slitPlane_iff,inv_re]
  exact Or.inl (div_pos hS (normSq_pos.mpr hSn))

/-- The `z`-derivative of the generating function is `-(coth t - 1/t)/2` times the function. -/
theorem whittakerBesselGenerating_hasDerivAt_z (μ z t : ℂ) :
    HasDerivAt (fun w => whittakerBesselGenerating μ w t)
      (-(cosh t/sinh t-t⁻¹)/2*whittakerBesselGenerating μ z t) z := by
  by_cases ht : t=0
  · subst t
    simpa [whittakerBesselGenerating] using hasDerivAt_const z (1:ℂ)
  · have h := (((hasDerivAt_id' z).const_mul (-(cosh t/sinh t-t⁻¹)/2)).cexp).mul_const
      ((t/sinh t)^(1-2*μ))
    convert h using 1
    · funext w
      simp only [whittakerBesselGenerating,ht,↓reduceIte]
      congr 2; ring
    · simp only [whittakerBesselGenerating,ht,↓reduceIte]
      have he : -(cosh t/sinh t-t⁻¹)/2*z = -z/2*(cosh t/sinh t-t⁻¹) := by ring
      rw [he]
      ring

/-- `∂_z G(μ,z,t) = -(coth t - 1/t)/2 · G(μ,z,t)`. -/
theorem whittakerBesselGenerating_deriv_z (μ z t : ℂ) :
    deriv (fun w => whittakerBesselGenerating μ w t) z =
      -(cosh t/sinh t-t⁻¹)/2*whittakerBesselGenerating μ z t :=
  (whittakerBesselGenerating_hasDerivAt_z μ z t).deriv

/-- `∂_z² G(μ,z,t) = (coth t - 1/t)²/4 · G(μ,z,t)`. -/
theorem whittakerBesselGenerating_iteratedDeriv_two_z (μ z t : ℂ) :
    iteratedDeriv 2 (fun w => whittakerBesselGenerating μ w t) z =
      (cosh t/sinh t-t⁻¹)^2/4*whittakerBesselGenerating μ z t := by
  have he : deriv (fun w => whittakerBesselGenerating μ w t) =
      fun w => -(cosh t/sinh t-t⁻¹)/2*whittakerBesselGenerating μ w t :=
    funext fun w => whittakerBesselGenerating_deriv_z μ w t
  rw [iteratedDeriv_succ,iteratedDeriv_one,he]
  rw [((whittakerBesselGenerating_hasDerivAt_z μ z t).const_mul
    (-(cosh t/sinh t-t⁻¹)/2)).deriv]
  ring

/-- For `0 < |t| < 1`, the `t`-derivative of the generating function satisfies a first-order PDE
linking it to its `z`-derivatives. -/
theorem whittakerBesselGenerating_hasDerivAt_t {μ z t : ℂ} (ht : t ≠ 0) (hsmall : ‖t‖ < 1) :
    HasDerivAt (whittakerBesselGenerating μ z)
      (2*z*iteratedDeriv 2 (fun w => whittakerBesselGenerating μ w t) z -
        2*z/t*deriv (fun w => whittakerBesselGenerating μ w t) z -
        2*(2*μ-1)*deriv (fun w => whittakerBesselGenerating μ w t) z -
        z/2*whittakerBesselGenerating μ z t) t := by
  have hbase := whittakerBessel_base_mem_slit ht hsmall
  have hbase0 := slitPlane_ne_zero hbase
  have hsh : sinh t ≠ 0 := fun h0 => hbase0 (by rw [h0,div_zero])
  have hquot := (Complex.hasDerivAt_cosh t).div (Complex.hasDerivAt_sinh t) hsh
  have hexp := ((hquot.sub ((hasDerivAt_id' t).inv ht)).const_mul (-z/2)).cexp
  have hpow := ((hasDerivAt_id' t).div (Complex.hasDerivAt_sinh t) hsh).cpow_const
    (c:=1-2*μ) hbase
  have h := hexp.mul hpow
  have heq : whittakerBesselGenerating μ z =ᶠ[𝓝 t]
      fun v => exp (-z/2*(cosh v/sinh v-v⁻¹))*(v/sinh v)^(1-2*μ) := by
    filter_upwards [eventually_ne_nhds ht] with v hv
    simp [whittakerBesselGenerating,hv]
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  rw [whittakerBesselGenerating_deriv_z,whittakerBesselGenerating_iteratedDeriv_two_z]
  simp only [whittakerBesselGenerating,ht,↓reduceIte,Pi.div_apply,Pi.sub_apply,Pi.inv_apply]
  rw [Complex.cpow_sub (1-2*μ) 1 hbase0,Complex.cpow_one]
  generalize exp (-z/2*(cosh t/sinh t-t⁻¹)) = E
  generalize (t/sinh t)^(1-2*μ) = P
  field_simp [ht,hsh]
  ring_nf


/-- The `j`-th `z`-derivative `(-(coth t - 1/t)/2)^j G(μ,z,t)` of the generating function. -/
private noncomputable def whittakerGenD (μ : ℂ) (j : ℕ) (z t : ℂ) : ℂ :=
  (-(cosh t/sinh t-t⁻¹)/2)^j*whittakerBesselGenerating μ z t

/-- The `s`-th Taylor coefficient at `t = 0` of the `j`-th `z`-derivative of the generating
function. -/
private noncomputable def whittakerTaylorD (μ : ℂ) (j : ℕ) (z : ℂ) (s : ℕ) : ℂ :=
  iteratedDeriv s (whittakerGenD μ j z) 0/s.factorial

/-- Each `z`-derivative of the generating function is holomorphic in `t` on the unit disc. -/
private lemma whittakerGenD_t_diff (μ : ℂ) (j : ℕ) (z : ℂ) :
    DifferentiableOn ℂ (whittakerGenD μ j z) (Metric.ball 0 1) := by
  exact ((((whittakerBessel_core_analytic.1.neg).div_const 2).pow j).mul
    (whittakerBesselGenerating_differentiableOn μ z))

/-- Each `z`-derivative of the generating function is jointly continuous in `(z, t)` for `|t| < 1`.
-/
private lemma whittakerGenD_joint_cont (μ : ℂ) (j : ℕ) {z t : ℂ} (ht : ‖t‖ < 1) :
    ContinuousAt (fun p : ℂ × ℂ => whittakerGenD μ j p.1 p.2) (z,t) := by
  have ht' : t ∈ Metric.ball (0:ℂ) 1 := by simpa using ht
  have hA : ContinuousAt (fun p : ℂ × ℂ => cosh p.2/sinh p.2-p.2⁻¹) (z,t) :=
    (whittakerBessel_core_analytic.1.differentiableAt
      (Metric.isOpen_ball.mem_nhds ht')).continuousAt.comp (x:=(z,t)) continuousAt_snd
  exact (((hA.neg.div_const 2).pow j).mul (whittakerBesselGenerating_joint_continuousAt μ ht))

/-- Differentiating `whittakerGenD μ j` in `z` gives `whittakerGenD μ (j+1)`. -/
private lemma whittakerGenD_z_deriv (μ : ℂ) (j : ℕ) (z t : ℂ) :
    HasDerivAt (fun w => whittakerGenD μ j w t) (whittakerGenD μ (j+1) z t) z := by
  convert (whittakerBesselGenerating_hasDerivAt_z μ z t).const_mul
    ((-(cosh t/sinh t-t⁻¹)/2)^j) using 1
  · rfl
  · simp only [whittakerGenD,pow_succ]
    ring

/-- The Taylor coefficients commute with `z`-differentiation: `∂_z D_j(s) = D_{j+1}(s)`. -/
private lemma whittakerTaylorD_hasDerivAt (μ : ℂ) (j s : ℕ) (z : ℂ) :
    HasDerivAt (fun w => whittakerTaylorD μ j w s) (whittakerTaylorD μ (j+1) z s) z := by
  have hdt (j : ℕ) (z : ℂ) : DifferentiableOn ℂ (whittakerGenD μ j z)
      (Metric.closedBall 0 (1/2)) := by
    apply (whittakerGenD_t_diff μ j z).mono
    intro t ht
    have ht' : ‖t‖ ≤ 1/2 := by simpa using ht
    simpa using (show ‖t‖ < 1 by linarith)
  have h := Complex.hasDerivAt_iteratedDeriv_param (G:=whittakerGenD μ j)
    (Gz:=whittakerGenD μ (j+1)) (r:=1/2) (by norm_num)
    (fun z t ht => whittakerGenD_joint_cont μ j (by rw [ht];norm_num))
    (fun z t ht => whittakerGenD_joint_cont μ (j+1) (by rw [ht];norm_num))
    (hdt j) (hdt (j+1)) (fun z t _ => whittakerGenD_z_deriv μ j z t) s z
  exact h.div_const _

/-- On a closed disc in `z`, the Taylor coefficients `D_j(s)` grow at most like `M 2^s`. -/
private lemma whittakerTaylorD_uniform_bound (μ : ℂ) (j : ℕ) (R : ℝ) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ z ∈ Metric.closedBall (0:ℂ) R,∀ s : ℕ,
      ‖whittakerTaylorD μ j z s‖ ≤ M*2^s := by
  have hdt (z : ℂ) : DifferentiableOn ℂ (whittakerGenD μ j z)
      (Metric.closedBall 0 (1/2)) := by
    apply (whittakerGenD_t_diff μ j z).mono
    intro t ht
    have ht' : ‖t‖ ≤ 1/2 := by simpa using ht
    simpa using (show ‖t‖ < 1 by linarith)
  obtain ⟨M,hM,hbd⟩ := Complex.exists_uniform_norm_taylorCoeff_le (G:=whittakerGenD μ j)
    (r:=1/2) (by norm_num)
    (fun z t ht => whittakerGenD_joint_cont μ j (by rw [ht];norm_num)) hdt 0 R
  refine ⟨M,hM,fun z hz s => ?_⟩
  have h := hbd z hz s
  simpa only [whittakerTaylorD,one_div,inv_pow,div_inv_eq_mul] using h


/-- Each `z`-derivative of the generating function is analytic in `t` for `|t| < 1`. -/
private lemma whittakerGenD_analyticAt (μ : ℂ) (j : ℕ) (z : ℂ) {t : ℂ} (ht : ‖t‖ < 1) :
    AnalyticAt ℂ (whittakerGenD μ j z) t :=
  (whittakerGenD_t_diff μ j z).analyticOnNhd Metric.isOpen_ball t (by simpa using ht)

/-- The zeroth `z`-derivative is the generating function itself. -/
private lemma whittakerGenD_zero (μ z : ℂ) : whittakerGenD μ 0 z=whittakerBesselGenerating μ z := by
  funext t
  simp [whittakerGenD]

/-- `(t f)^{(n+1)}(0) = (n+1) f^{(n)}(0)` for `f` analytic at `0`. -/
private lemma buchholz_iteratedDeriv_id_mul_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    iteratedDeriv (n+1) (fun t : ℂ => t*f t) 0 = (n+1)*iteratedDeriv n f 0 := by
  rw [iteratedDeriv_fun_mul (f:=fun t:ℂ=>t) (g:=f) contDiffAt_id hf.contDiffAt]
  simp only [iteratedDeriv_fun_id_zero,mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  simp [show 1 < n+1+1 by omega]

/-- The PDE of the generating function in the form `t ∂_t G + 2z D₁ = 2z t D₂ - 2(2μ-1) t D₁ - (z/2)
t D₀`. -/
private lemma whittakerBesselGenerating_pde {μ z t : ℂ} (ht : ‖t‖ < 1) :
    t*deriv (whittakerBesselGenerating μ z) t+2*z*whittakerGenD μ 1 z t =
      2*z*(t*whittakerGenD μ 2 z t)-2*(2*μ-1)*(t*whittakerGenD μ 1 z t)-
        z/2*(t*whittakerGenD μ 0 z t) := by
  by_cases ht0 : t=0
  · subst t
    simp [whittakerGenD]
  · rw [(whittakerBesselGenerating_hasDerivAt_t ht0 ht).deriv,
      whittakerBesselGenerating_deriv_z,whittakerBesselGenerating_iteratedDeriv_two_z]
    simp only [whittakerGenD,pow_zero,pow_one,one_mul]
    field_simp
    ring

/-- The recurrence for the Taylor coefficients `D_j(s)` obtained from the generating-function PDE.
-/
private lemma whittakerTaylorD_recurrence (μ z : ℂ) (s : ℕ) :
    (s+1)*whittakerTaylorD μ 0 z (s+1)+2*z*whittakerTaylorD μ 1 z (s+1) =
      2*z*whittakerTaylorD μ 2 z s-2*(2*μ-1)*whittakerTaylorD μ 1 z s-
        z/2*whittakerTaylorD μ 0 z s := by
  let G := whittakerBesselGenerating μ z
  have hG : AnalyticAt ℂ G 0 := by
    exact (whittakerBesselGenerating_differentiableOn μ z).analyticOnNhd Metric.isOpen_ball 0 (by simp)
  have hF (j : ℕ) : AnalyticAt ℂ (whittakerGenD μ j z) 0 :=
    whittakerGenD_analyticAt μ j z (by simp)
  have hX (j : ℕ) : AnalyticAt ℂ (fun t : ℂ => t*whittakerGenD μ j z t) 0 :=
    analyticAt_id.mul (hF j)
  have he : (fun t : ℂ => t*deriv G t+2*z*whittakerGenD μ 1 z t) =ᶠ[𝓝 0]
      (fun t : ℂ => 2*z*(t*whittakerGenD μ 2 z t)-2*(2*μ-1)*(t*whittakerGenD μ 1 z t)-
        z/2*(t*whittakerGenD μ 0 z t)) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1)] with t ht
    exact whittakerBesselGenerating_pde (by simpa using ht)
  have h := he.iteratedDeriv_eq (s+1)
  have hL1 : AnalyticAt ℂ (fun t : ℂ => t*deriv G t) 0 := analyticAt_id.mul hG.deriv
  have hL2 : AnalyticAt ℂ (fun t : ℂ => 2*z*whittakerGenD μ 1 z t) 0 :=
    analyticAt_const.mul (hF 1)
  have hR1 : AnalyticAt ℂ (fun t : ℂ => 2*z*(t*whittakerGenD μ 2 z t)) 0 :=
    analyticAt_const.mul (hX 2)
  have hR2 : AnalyticAt ℂ (fun t : ℂ => 2*(2*μ-1)*(t*whittakerGenD μ 1 z t)) 0 :=
    analyticAt_const.mul (hX 1)
  have hR3 : AnalyticAt ℂ (fun t : ℂ => z/2*(t*whittakerGenD μ 0 z t)) 0 :=
    analyticAt_const.mul (hX 0)
  rw [iteratedDeriv_fun_add hL1.contDiffAt hL2.contDiffAt] at h
  change _ = iteratedDeriv (s+1)
    (((fun t : ℂ => 2*z*(t*whittakerGenD μ 2 z t)) -
      (fun t : ℂ => 2*(2*μ-1)*(t*whittakerGenD μ 1 z t))) -
      (fun t : ℂ => z/2*(t*whittakerGenD μ 0 z t))) 0 at h
  rw [iteratedDeriv_sub (hR1.sub hR2).contDiffAt hR3.contDiffAt,
    iteratedDeriv_sub hR1.contDiffAt hR2.contDiffAt] at h
  simp only [iteratedDeriv_const_mul_field] at h
  rw [buchholz_iteratedDeriv_id_mul_zero hG.deriv,
    buchholz_iteratedDeriv_id_mul_zero (hF 2),buchholz_iteratedDeriv_id_mul_zero (hF 1),
    buchholz_iteratedDeriv_id_mul_zero (hF 0)] at h
  simp only [←iteratedDeriv_succ'] at h
  dsimp only [G] at h
  rw [←whittakerGenD_zero μ z] at h
  dsimp only [whittakerTaylorD]
  have hfac : (s.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.factorial_ne_zero
  have hs : (s+1:ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  linear_combination 2*h


/-- The Buchholz coefficient `(-1/2)^s z^s D₀(s)`. -/
private noncomputable def buchholzC (μ : ℂ) (s : ℕ) (z : ℂ) : ℂ :=
  (-1/2:ℂ)^s*z^s*whittakerTaylorD μ 0 z s

/-- The `z`-derivative of the Buchholz coefficient `buchholzC`. -/
private noncomputable def buchholzC1 (μ : ℂ) (s : ℕ) (z : ℂ) : ℂ :=
  (-1/2:ℂ)^s*((s:ℂ)*z^(s-1)*whittakerTaylorD μ 0 z s+z^s*whittakerTaylorD μ 1 z s)

/-- The second `z`-derivative of the Buchholz coefficient `buchholzC`. -/
private noncomputable def buchholzC2 (μ : ℂ) (s : ℕ) (z : ℂ) : ℂ :=
  (-1/2:ℂ)^s*((s:ℂ)*(s-1:ℕ)*z^(s-2)*whittakerTaylorD μ 0 z s+
    2*s*z^(s-1)*whittakerTaylorD μ 1 z s+z^s*whittakerTaylorD μ 2 z s)

/-- `buchholzC μ s` has `z`-derivative `buchholzC1 μ s`. -/
private lemma buchholzC_hasDerivAt (μ : ℂ) (s : ℕ) (z : ℂ) :
    HasDerivAt (buchholzC μ s) (buchholzC1 μ s z) z := by
  convert (((hasDerivAt_id' z).pow s).mul (whittakerTaylorD_hasDerivAt μ 0 s z)).const_mul
    ((-1/2:ℂ)^s) using 1
  · funext w
    simp only [buchholzC,Pi.mul_apply,Pi.pow_apply]
    ring
  · simp only [buchholzC1,Pi.pow_apply,Nat.zero_add,mul_one]

/-- `buchholzC1 μ s` has `z`-derivative `buchholzC2 μ s`. -/
private lemma buchholzC1_hasDerivAt (μ : ℂ) (s : ℕ) (z : ℂ) :
    HasDerivAt (buchholzC1 μ s) (buchholzC2 μ s z) z := by
  have h := (((((hasDerivAt_id' z).pow (s-1)).const_mul (s:ℂ)).mul
    (whittakerTaylorD_hasDerivAt μ 0 s z)).add
    (((hasDerivAt_id' z).pow s).mul (whittakerTaylorD_hasDerivAt μ 1 s z))).const_mul
      ((-1/2:ℂ)^s)
  convert h using 1
  · rfl
  · simp only [buchholzC2,Nat.sub_sub,Pi.pow_apply,Nat.zero_add,Nat.reduceAdd,mul_one]
    ring

/-- `z C'_s(z) = (-1/2)^s z^s (s D₀(s) + z D₁(s))`. -/
private lemma buchholzC_weighted_deriv (μ : ℂ) (s : ℕ) (z : ℂ) :
    z*buchholzC1 μ s z=(-1/2:ℂ)^s*z^s*((s:ℂ)*whittakerTaylorD μ 0 z s+
      z*whittakerTaylorD μ 1 z s) := by
  cases s with
  | zero => simp [buchholzC1]
  | succ s => simp only [buchholzC1,Nat.add_sub_cancel,pow_succ];ring

/-- `z² C''_s(z) = (-1/2)^s z^s (s(s-1) D₀(s) + 2sz D₁(s) + z² D₂(s))`. -/
private lemma buchholzC_weighted_second (μ : ℂ) (s : ℕ) (z : ℂ) :
    z^2*buchholzC2 μ s z=(-1/2:ℂ)^s*z^s*((s:ℂ)*(s-1)*whittakerTaylorD μ 0 z s+
      2*s*z*whittakerTaylorD μ 1 z s+z^2*whittakerTaylorD μ 2 z s) := by
  cases s with
  | zero => simp [buchholzC2]
  | succ s => cases s with
    | zero => simp [buchholzC2];ring
    | succ s =>
      simp only [buchholzC2,show s+1+1-2=s by omega,show s+1+1-1=s+1 by omega,
        Nat.cast_add,Nat.cast_one,pow_succ]
      ring

/-- The auxiliary combination `(-1/2)^s z^s (s D₀(s) + 2z D₁(s))`. -/
private noncomputable def buchholzA (μ : ℂ) (s : ℕ) (z : ℂ) : ℂ :=
  (-1/2:ℂ)^s*z^s*((s:ℂ)*whittakerTaylorD μ 0 z s+2*z*whittakerTaylorD μ 1 z s)

/-- `A_s = 2z C'_s - s C_s`. -/
private lemma buchholzA_eq (μ : ℂ) (s : ℕ) (z : ℂ) :
    buchholzA μ s z=2*z*buchholzC1 μ s z-(s:ℂ)*buchholzC μ s z := by
  rw [show 2*z*buchholzC1 μ s z=2*(z*buchholzC1 μ s z) by ring,buchholzC_weighted_deriv]
  simp only [buchholzA,buchholzC]
  ring

/-- The differential recurrence `A_{s+1} = -z² C''_s + (2s+2μ-1) z C'_s - s(s+2μ) C_s + (z²/4) C_s`
for the Buchholz coefficients. -/
private lemma buchholzC_recurrence (μ : ℂ) (s : ℕ) (z : ℂ) :
    buchholzA μ (s+1) z = -z^2*buchholzC2 μ s z+(2*s+2*μ-1)*z*buchholzC1 μ s z-
      (s:ℂ)*(s+2*μ)*buchholzC μ s z+z^2/4*buchholzC μ s z := by
  rw [show -z^2*buchholzC2 μ s z= -(z^2*buchholzC2 μ s z) by ring,
    show (2*s+2*μ-1)*z*buchholzC1 μ s z=(2*s+2*μ-1)*(z*buchholzC1 μ s z) by ring,
    buchholzC_weighted_second,buchholzC_weighted_deriv]
  simp only [buchholzA,buchholzC,pow_succ,Nat.cast_add,Nat.cast_one]
  have h := whittakerTaylorD_recurrence μ z s
  linear_combination ((-1/2:ℂ)^s*z^(s+1)*(-1/2))*h



/-- The series with terms `(fun s : ℕ => whittakerBesselCoeff μ z s * (-t / z) ^ s)` converges to
`(exp (-z / 2 * (cosh t / sinh t - 1 / t)) * (t / sinh t) ^ (1 - 2 * μ))`. -/
@[dlmf 13.24.E3]
theorem whittakerBesselCoeff_hasSum {μ z t : ℂ} (ht : t ≠ 0) (hz : z ≠ 0)
    (hsmall : ‖t‖ < 1) :
    HasSum (fun s : ℕ => whittakerBesselCoeff μ z s * (-t / z) ^ s)
      (exp (-z / 2 * (cosh t / sinh t - 1 / t)) * (t / sinh t) ^ (1 - 2 * μ)) := by
  have hGd := whittakerBesselGenerating_differentiableOn μ z
  have hT := Complex.hasSum_taylorSeries_on_ball hGd (z := t) (by simpa using hsmall)
  convert hT using 1
  · funext s
    simp only [whittakerBesselCoeff, sub_zero, smul_eq_mul]
    rw [div_pow, mul_div_assoc', mul_assoc, ← mul_pow, show -z * -t = z * t by ring, mul_pow]
    have hf : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  · simp only [whittakerBesselGenerating, ht, ↓reduceIte, one_div]

/-- Exponential coefficient bound from the generating function inside its disk. -/
theorem exists_norm_whittakerBesselCoeff_le (μ : ℂ) {z : ℂ} (hz : z ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℕ, ‖whittakerBesselCoeff μ z s‖ ≤ C*(2*‖z‖)^s := by
  have hs := (whittakerBesselCoeff_hasSum (μ := μ) (z := z) (t := 1/2)
    (by norm_num) hz (by norm_num)).summable.norm
  let C := ∑' s : ℕ, ‖whittakerBesselCoeff μ z s * (-(1/2:ℂ)/z)^s‖
  refine ⟨C, tsum_nonneg fun _ => norm_nonneg _, fun s => ?_⟩
  have h := hs.le_tsum s (fun _ _ => norm_nonneg _)
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hpow : 0 < (2*‖z‖)^s := pow_pos (by positivity) s
  have he : ‖whittakerBesselCoeff μ z s * (-(1/2:ℂ)/z)^s‖ =
      ‖whittakerBesselCoeff μ z s‖ / (2*‖z‖)^s := by
    simp only [norm_mul, norm_pow, norm_div, norm_neg]
    norm_num
    rw [div_div, div_pow, one_pow, ← mul_div_assoc, mul_one]
  rw [he] at h
  exact (div_le_iff₀ hpow).mp h

/-- Absolute convergence of the regularized form of the Buchholz series. -/
theorem summable_whittakerBessel_regularized (κ μ : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Summable fun s : ℕ => whittakerBesselCoeff μ z s / (2:ℂ)^s *
      regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*z)) := by
  obtain ⟨C, hC, hcoef⟩ := exists_norm_whittakerBesselCoeff_le μ hz
  have hs : Summable fun s : ℕ => ‖whittakerBesselCoeff μ z s‖ / s ! := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun s => ?_)
      ((Real.summable_pow_div_factorial (2*‖z‖)).mul_left C)
    exact (div_le_div_of_nonneg_right (hcoef s) (by positivity)).trans_eq (by ring)
  have ha : Summable fun s : ℕ => ‖whittakerBesselCoeff μ z s / (2:ℂ)^s‖ *
      ‖(1:ℂ)‖ ^ (0:ℕ) * ((2:ℝ)^s/s !) := by
    convert hs using 1
    funext s
    simp only [norm_div, norm_pow, norm_ofNat, pow_zero, mul_one]
    field_simp
  simpa using (hasSum_neumann (2*μ) (-(κ*z)) 1
    (fun s => whittakerBesselCoeff μ z s / (2:ℂ)^s) id (fun _ => 0) ha).summable

/-- Cancellation of principal powers in each Buchholz Bessel term. -/
theorem whittakerBessel_term_eq_regularized {κ z : ℂ} (hκ : κ ≠ 0) (hz : z ≠ 0)
    (μ : ℂ) (s : ℕ) :
    (2:ℂ)^(2*μ) * (2*(κ*z)^(1/2:ℂ))^(-(2*μ+s)) *
      besselJ (2*μ+s) (2*(κ*z)^(1/2:ℂ)) =
    1/(2:ℂ)^s * regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*z)) := by
  set x := 2*(κ*z)^(1/2:ℂ)
  have hx0 : x ≠ 0 := mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero hκ hz)))
  have hx2 : x^2/4 = κ*z := by
    dsimp only [x]
    rw [mul_pow, one_div, cpow_ofNat_inv_pow]
    ring
  rw [besselJ_eq_regularized, hx2]
  have hp : (x/2)^(2*μ+s) = x^(2*μ+s)/(2:ℂ)^(2*μ+s) := by
    simpa using div_ofReal_cpow (r := 2) (by norm_num) hx0 (2*μ+s)
  rw [hp, cpow_add _ _ two_ne_zero, cpow_natCast, cpow_neg]
  have hxpow : x^(2*μ+s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hx0)
  have h2pow : (2:ℂ)^(2*μ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have h2s : (2:ℂ)^s ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp

/-- The Buchholz sum has no residual principal-branch factors after normalization. -/
theorem whittakerBessel_series_eq_regularized {κ z : ℂ} (hκ : κ ≠ 0) (hz : z ≠ 0)
    (μ : ℂ) :
    (2:ℂ)^(2*μ) * (∑' s : ℕ, whittakerBesselCoeff μ z s *
      (2*(κ*z)^(1/2:ℂ))^(-(2*μ+s)) *
      besselJ (2*μ+s) (2*(κ*z)^(1/2:ℂ))) =
    ∑' s : ℕ, whittakerBesselCoeff μ z s / (2:ℂ)^s *
      regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*z)) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun s => ?_
  have h := whittakerBessel_term_eq_regularized hκ hz μ s
  linear_combination whittakerBesselCoeff μ z s * h

/-- The Bessel series in DLMF 13.24.2 is absolutely convergent. -/
theorem summable_whittakerM_besselJ_series {κ z : ℂ} (hκ : κ ≠ 0) (hz : z ≠ 0)
    (μ : ℂ) :
    Summable fun s : ℕ => ‖whittakerBesselCoeff μ z s *
      (2*(κ*z)^(1/2:ℂ))^(-(2*μ+s)) *
      besselJ (2*μ+s) (2*(κ*z)^(1/2:ℂ))‖ := by
  have h2pow : (2:ℂ)^(2*μ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hs := (summable_whittakerBessel_regularized κ μ hz).mul_left ((2:ℂ)^(2*μ))⁻¹
  apply Summable.norm
  refine hs.congr fun s => ?_
  have h := whittakerBessel_term_eq_regularized hκ hz μ s
  field_simp at h ⊢
  linear_combination -(whittakerBesselCoeff μ z s)*h
/-- The normalized Buchholz coefficient is the original coefficient divided by `2^s`. -/
private lemma buchholzC_eq (μ z : ℂ) (s : ℕ) :
    buchholzC μ s z = whittakerBesselCoeff μ z s / (2:ℂ)^s := by
  simp only [buchholzC,whittakerTaylorD,whittakerGenD_zero,whittakerBesselCoeff]
  have hp : (-1/2:ℂ)^s*z^s=(-z)^s/(2:ℂ)^s := by
    rw [← mul_pow,← div_pow]
    congr 1
    ring
  rw [hp]
  ring

/-- The shifted regularized `₀F₁` functions have a factorial bound on each closed disc. -/
private lemma buchholz_0F1_uniform_bound (κ ν : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖regularizedHGFun (∅ : Multiset ℂ) {ν+s+1} (-(κ*z))‖ ≤ M*(2^s/s !) := by
  obtain ⟨C,hC,hcoef⟩ := exists_norm_regularized0F1Coeff_le ν
  let T : ℝ := ∑' m : ℕ, (2*(‖κ‖*R))^m/(m ! : ℝ)
  have hT := Real.summable_pow_div_factorial (2*(‖κ‖*R))
  have hT0 : 0 ≤ T := tsum_nonneg fun _ => by positivity
  refine ⟨C*T,mul_nonneg hC hT0,fun s z hz => ?_⟩
  have hs := (hasFPowerSeriesOnBall_regularized0F1 (ν+s+1)).hasSum_mul_pow
    (z:= -(κ*z)) (by simp)
  calc ‖regularizedHGFun (∅ : Multiset ℂ) {ν+s+1} (-(κ*z))‖
      ≤ C*(2^s/s !)*T := by
        refine hs.norm_le_of_bounded (hT.hasSum.mul_left (C*(2^s/s !))) fun m => ?_
        simp only [norm_mul,norm_pow,norm_neg]
        calc ‖regularizedHGFunCoeff (∅ : Multiset ℂ) {ν+s+1} m‖*(‖κ‖*‖z‖)^m
            ≤ C*(2^s/s !)*(2^m/m !)*(‖κ‖*R)^m := by gcongr; exact hcoef s m
          _ = C*(2^s/s !)*((2*(‖κ‖*R))^m/(m ! : ℝ)) := by rw [mul_pow]; ring
    _ = _ := by ring

/-- The factors `z^s` cancel the Cauchy growth of the Taylor coefficients. -/
private lemma buchholzC_uniform_bound (μ : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖buchholzC μ s z‖ ≤ M*R^s := by
  obtain ⟨M,hM,hcoef⟩ := whittakerTaylorD_uniform_bound μ 0 R
  refine ⟨M,hM,fun s z hz => ?_⟩
  have ht := hcoef z (by simpa using hz) s
  simp only [buchholzC,norm_mul,norm_pow,norm_div,norm_neg,norm_one,norm_ofNat]
  calc (1/2:ℝ)^s*‖z‖^s*‖whittakerTaylorD μ 0 z s‖
      ≤ (1/2:ℝ)^s*R^s*(M*2^s) := by gcongr
    _ = M*R^s := by rw [show (1/2:ℝ)^s*R^s*(M*2^s)=
        M*R^s*((1/2:ℝ)*2)^s by rw [mul_pow]; ring]; norm_num

/-- An exponential bound also absorbs the factor `s` in the telescoping coefficient. -/
private lemma buchholzA_uniform_bound (μ : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖buchholzA μ s z‖ ≤ M*(2*R)^s := by
  obtain ⟨M₀,hM₀,h₀⟩ := whittakerTaylorD_uniform_bound μ 0 R
  obtain ⟨M₁,hM₁,h₁⟩ := whittakerTaylorD_uniform_bound μ 1 R
  have hn : ∀ s : ℕ, (s:ℝ) ≤ 2^s := by
    intro s
    induction s with
    | zero => norm_num
    | succ s ih =>
      have hp : (1:ℝ) ≤ 2^s := one_le_pow₀ (by norm_num)
      simp only [Nat.cast_succ,pow_succ]
      linarith
  refine ⟨M₀+2*R*M₁,by positivity,fun s z hz => ?_⟩
  have hz' : z ∈ Metric.closedBall (0:ℂ) R := by simpa using hz
  calc ‖buchholzA μ s z‖
      ≤ (1/2:ℝ)^s*R^s*((s:ℝ)*(M₀*2^s)+2*R*(M₁*2^s)) := by
        simp only [buchholzA,norm_mul,norm_pow,norm_div,norm_neg,norm_one,norm_ofNat]
        gcongr
        exact (norm_add_le _ _).trans (add_le_add
          (by simp only [norm_mul,Complex.norm_natCast]; gcongr; exact h₀ z hz' s)
          (by simp only [norm_mul,norm_ofNat]; gcongr; exact h₁ z hz' s))
    _ ≤ (1/2:ℝ)^s*R^s*(2^s*(M₀*2^s)+2^s*(2*R*(M₁*2^s))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (hn s) (by positivity)
        · exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    _ = (M₀+2*R*M₁)*(2*R)^s := by
        rw [mul_pow]
        have hp : (1/2:ℝ)^s*2^s=1 := by rw [← mul_pow]; norm_num
        calc _ = (M₀+2*R*M₁)*(2^s*R^s)*((1/2:ℝ)^s*2^s) := by ring
             _ = _ := by rw [hp,mul_one]

/-- The `s`-th summand of the branch-free Buchholz expansion. -/
private noncomputable def buchholzTerm (κ μ : ℂ) (s : ℕ) (z : ℂ) : ℂ :=
  buchholzC μ s z*regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*z))

/-- Every Buchholz summand is entire in its argument. -/
private lemma buchholzTerm_differentiable (κ μ : ℂ) (s : ℕ) :
    Differentiable ℂ (buchholzTerm κ μ s) := by
  intro z
  exact ((buchholzC_hasDerivAt μ s z).differentiableAt.mul
    ((analyticAt_regularized0F1 _ _).differentiableAt.comp z
      (((hasDerivAt_id z).const_mul κ).neg.differentiableAt)))

/-- On every disc the Buchholz summands admit a common summable majorant. -/
private lemma buchholzTerm_uniform_bound (κ μ : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ s : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖buchholzTerm κ μ s z‖ ≤ u s := by
  obtain ⟨M,hM,hC⟩ := buchholzC_uniform_bound μ hR
  obtain ⟨N,hN,hF⟩ := buchholz_0F1_uniform_bound κ (2*μ) hR
  refine ⟨fun s => M*N*((2*R)^s/s !),
    (Real.summable_pow_div_factorial (2*R)).mul_left _,fun s z hz => ?_⟩
  calc ‖buchholzTerm κ μ s z‖ = ‖buchholzC μ s z‖*
        ‖regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*z))‖ := norm_mul _ _
    _ ≤ M*R^s*(N*(2^s/s !)) := by gcongr; exact hC s z hz; exact hF s z hz
    _ = _ := by
        change M*R^s*(N*(2^s/(s ! : ℝ)))=M*N*((2*R)^s/(s ! : ℝ))
        rw [mul_pow]
        ring

/-- The boundary term of the Buchholz telescoping relation tends to zero. -/
private lemma buchholz_boundary_tendsto (κ μ z : ℂ) :
    Tendsto (fun s : ℕ => buchholzA μ s z*
      regularizedHGFun (∅ : Multiset ℂ) {2*μ+s} (-(κ*z))) atTop (𝓝 0) := by
  let R := ‖z‖
  obtain ⟨M,hM,hA⟩ := buchholzA_uniform_bound μ (norm_nonneg z)
  obtain ⟨N,hN,hF⟩ := buchholz_0F1_uniform_bound κ (2*μ-1) (norm_nonneg z)
  apply Summable.tendsto_atTop_zero
  refine Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial (4*R)).mul_left (M*N)) fun s => ?_
  calc ‖buchholzA μ s z*regularizedHGFun (∅ : Multiset ℂ) {2*μ+s} (-(κ*z))‖
      ≤ M*(2*R)^s*(N*(2^s/s !)) := by
        rw [norm_mul]
        gcongr
        · exact hA s z le_rfl
        · simpa only [show 2*μ-1+s+1=2*μ+s by ring] using hF s z le_rfl
    _ = M*N*((4*R)^s/s !) := by
        simp only [show 4*R=(2*R)*2 by ring,mul_pow]
        ring

/-- Differentiating a normalized Buchholz summand raises the `₀F₁` order by one. -/
private lemma buchholzTerm_deriv (κ μ : ℂ) (s : ℕ) (z : ℂ) :
    deriv (buchholzTerm κ μ s) z =
      buchholzC1 μ s z*regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*z))-
      κ*buchholzC μ s z*regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1+1} (-(κ*z)) := by
  have hd := (buchholzC_hasDerivAt μ s z).mul
    ((hasDerivAt_regularized0F1 (2*μ+s+1) (-(κ*z))).comp z
      (((hasDerivAt_id z).const_mul κ).neg))
  convert hd.deriv using 1
  · congr 1
  · simp only [Pi.neg_apply,Function.comp_apply,id_eq,mul_one]
    ring

/-- The second derivative of a Buchholz summand involves only three adjacent `₀F₁` orders. -/
private lemma buchholzTerm_second (κ μ : ℂ) (s : ℕ) (z : ℂ) :
    deriv (deriv (buchholzTerm κ μ s)) z =
      buchholzC2 μ s z*regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*z))-
      2*κ*buchholzC1 μ s z*regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1+1} (-(κ*z))+
      κ^2*buchholzC μ s z*regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1+1+1} (-(κ*z)) := by
  have hφ (c : ℂ) := (hasDerivAt_regularized0F1 c (-(κ*z))).comp z
    (((hasDerivAt_id z).const_mul κ).neg)
  have hd := ((buchholzC1_hasDerivAt μ s z).mul (hφ (2*μ+s+1))).sub
    (((buchholzC_hasDerivAt μ s z).const_mul κ).mul (hφ (2*μ+s+1+1)))
  have he : deriv (buchholzTerm κ μ s) = fun w =>
      buchholzC1 μ s w*regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*w))-
      κ*buchholzC μ s w*regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1+1} (-(κ*w)) :=
    funext (buchholzTerm_deriv κ μ s)
  rw [he]
  convert hd.deriv using 1
  · congr 1
  · simp only [Pi.neg_apply,Function.comp_apply,id_eq,mul_one]
    ring

/-- Applying the normalized Whittaker operator to one Buchholz term gives a telescoping
 difference of adjacent orders. -/
private lemma buchholzTerm_ode (κ μ : ℂ) (s : ℕ) (z : ℂ) :
    z*(z*deriv (deriv (buchholzTerm κ μ s)) z+(2*μ+1)*deriv (buchholzTerm κ μ s) z+
      (κ-z/4)*buchholzTerm κ μ s z) =
      buchholzA μ s z*regularizedHGFun (∅ : Multiset ℂ) {2*μ+s} (-(κ*z))-
      buchholzA μ (s+1) z*regularizedHGFun (∅ : Multiset ℂ) {2*μ+((s+1:ℕ):ℂ)} (-(κ*z)) := by
  rw [buchholzTerm_deriv,buchholzTerm_second,buchholzTerm]
  have hc := regularized0F1_contiguous (2*μ+s) (-(κ*z))
  have hd := regularized0F1_contiguous (2*μ+s+1) (-(κ*z))
  have ha := buchholzA_eq μ s z
  have hr := buchholzC_recurrence μ s z
  have he : 2*μ+((s+1:ℕ):ℂ)=2*μ+s+1 := by push_cast; ring
  rw [he]
  linear_combination -(buchholzA μ s z)*hc+
    (κ*z*buchholzC μ s z)*hd+
    (regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*z)))*hr+
    (-(2*μ+s)*regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*z))+
      κ*z*regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1+1} (-(κ*z)))*ha

/-- The initial coefficient in the Buchholz telescoping difference vanishes. -/
private lemma buchholzA_zero (μ z : ℂ) : buchholzA μ 0 z=0 := by
  simp [buchholzA,whittakerTaylorD,whittakerGenD,whittakerBesselGenerating]

/-- The partial sums satisfy the normalized Whittaker equation up to a single boundary term. -/
private lemma buchholz_partial_ode (κ μ : ℂ) (N : ℕ) (z : ℂ) :
    z*(z*deriv (deriv (fun w => ∑ s ∈ Finset.range N, buchholzTerm κ μ s w)) z+
      (2*μ+1)*deriv (fun w => ∑ s ∈ Finset.range N, buchholzTerm κ μ s w) z+
      (κ-z/4)*(∑ s ∈ Finset.range N, buchholzTerm κ μ s z)) =
      -(buchholzA μ N z*regularizedHGFun (∅ : Multiset ℂ) {2*μ+N} (-(κ*z))) := by
  have hder : deriv (fun w => ∑ s ∈ Finset.range N, buchholzTerm κ μ s w) =
      fun w => ∑ s ∈ Finset.range N, deriv (buchholzTerm κ μ s) w := by
    funext w
    exact deriv_fun_sum fun s _ => buchholzTerm_differentiable κ μ s w
  rw [hder,deriv_fun_sum (fun s _ => (buchholzTerm_differentiable κ μ s).deriv z)]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  calc (∑ s ∈ Finset.range N,
      z*(z*deriv (deriv (buchholzTerm κ μ s)) z+(2*μ+1)*deriv (buchholzTerm κ μ s) z+
        (κ-z/4)*buchholzTerm κ μ s z)) =
      ∑ s ∈ Finset.range N,
        (buchholzA μ s z*regularizedHGFun (∅ : Multiset ℂ) {2*μ+s} (-(κ*z))-
          buchholzA μ (s+1) z*regularizedHGFun (∅ : Multiset ℂ) {2*μ+((s+1:ℕ):ℂ)} (-(κ*z))) := by
        exact Finset.sum_congr rfl fun s _ => buchholzTerm_ode κ μ s z
    _ = _ := by rw [Finset.sum_range_sub']; simp [buchholzA_zero]

/-- The Buchholz series defines an entire function. -/
private lemma buchholz_sum_differentiable (κ μ : ℂ) :
    Differentiable ℂ (fun z => ∑' s, buchholzTerm κ μ s z) := by
  intro z
  obtain ⟨u,hu,hb⟩ := buchholzTerm_uniform_bound κ μ (show 0 ≤ ‖z‖+1 by positivity)
  have hd := Complex.differentiableOn_tsum_of_summable_norm hu
    (fun s => (buchholzTerm_differentiable κ μ s).differentiableOn) Metric.isOpen_ball
    (fun s w hw => hb s w (by simpa using (mem_ball_zero_iff.mp hw).le))
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp : z ∈ Metric.ball (0:ℂ) (‖z‖+1)))

/-- Uniform convergence on a disc is preserved through two complex differentiations, so the
 telescoping differential equation passes to the full Buchholz sum. -/
private lemma buchholz_sum_weighted_ode (κ μ z : ℂ) :
    z*(z*deriv (deriv (fun w => ∑' s, buchholzTerm κ μ s w)) z+
      (2*μ+1)*deriv (fun w => ∑' s, buchholzTerm κ μ s w) z+
      (κ-z/4)*(∑' s, buchholzTerm κ μ s z))=0 := by
  let R := ‖z‖+1
  let P : ℕ → ℂ → ℂ := fun N w => ∑ s ∈ Finset.range N, buchholzTerm κ μ s w
  let S : ℂ → ℂ := fun w => ∑' s, buchholzTerm κ μ s w
  have hz : z ∈ Metric.ball (0:ℂ) R := by simp [R]
  obtain ⟨u,hu,hb⟩ := buchholzTerm_uniform_bound κ μ (show 0 ≤ R by positivity)
  have hconv : TendstoLocallyUniformlyOn P S atTop (Metric.ball (0:ℂ) R) := by
    have hf := (tendstoUniformlyOn_tsum hu (fun s w hw =>
      hb s w (mem_ball_zero_iff.mp hw).le)).tendstoLocallyUniformlyOn
    intro V hV w hw
    obtain ⟨t,ht,het⟩ := hf V hV w hw
    exact ⟨t,ht,tendsto_finset_range.eventually het⟩
  have hP (N : ℕ) : Differentiable ℂ (P N) :=
    Differentiable.fun_sum fun s _ => buchholzTerm_differentiable κ μ s
  have hdiff : ∀ᶠ N in atTop, DifferentiableOn ℂ (P N) (Metric.ball (0:ℂ) R) :=
    Eventually.of_forall fun N => (hP N).differentiableOn
  have hdiff' : ∀ᶠ N in atTop, DifferentiableOn ℂ (deriv (P N)) (Metric.ball (0:ℂ) R) :=
    Eventually.of_forall fun N => (hP N).deriv.differentiableOn
  have hconv' := hconv.deriv hdiff Metric.isOpen_ball
  have hconv'' := hconv'.deriv hdiff' Metric.isOpen_ball
  have ht : Tendsto (fun N => z*(z*deriv (deriv (P N)) z+
      (2*μ+1)*deriv (P N) z+(κ-z/4)*P N z)) atTop
      (𝓝 (z*(z*deriv (deriv S) z+(2*μ+1)*deriv S z+(κ-z/4)*S z))) :=
    (tendsto_const_nhds.mul ((tendsto_const_nhds.mul (hconv''.tendsto_at hz)).add
    (tendsto_const_nhds.mul (hconv'.tendsto_at hz)) |>.add
    (tendsto_const_nhds.mul (hconv.tendsto_at hz))))
  have ht' := (buchholz_boundary_tendsto κ μ z).neg
  have he := tendsto_nhds_unique (ht.congr' (Eventually.of_forall fun N =>
    buchholz_partial_ode κ μ N z)) ht'
  simpa using he

/-- The removable equation at the origin follows by continuity from the punctured plane. -/
private lemma buchholz_sum_ode (κ μ z : ℂ) :
    z*deriv (deriv (fun w => ∑' s, buchholzTerm κ μ s w)) z+
      (2*μ+1)*deriv (fun w => ∑' s, buchholzTerm κ μ s w) z+
      (κ-z/4)*(∑' s, buchholzTerm κ μ s z)=0 := by
  let S : ℂ → ℂ := fun w => ∑' s, buchholzTerm κ μ s w
  have hs := buchholz_sum_differentiable κ μ
  have hc : Continuous (fun w : ℂ =>
      w*deriv (deriv S) w+(2*μ+1)*deriv S w+(κ-w/4)*S w) := by
    exact ((continuous_id.mul hs.deriv.deriv.continuous).add
      (continuous_const.mul hs.deriv.continuous)).add
      ((continuous_const.sub (continuous_id.div_const 4)).mul hs.continuous)
  have he := Continuous.ext_on (dense_compl_singleton (0:ℂ)) hc continuous_const (fun w hw =>
    (mul_eq_zero.mp (buchholz_sum_weighted_ode κ μ w)).resolve_left (by simpa using hw))
  exact congrFun he z

/-- Taylor coefficients of an entire solution satisfy a two-step recurrence at the origin. -/
private lemma buchholz_normalized_ode_jet {f : ℂ → ℂ} (hf : Differentiable ℂ f) (b κ : ℂ)
    (hode : ∀ z, z*deriv (deriv f) z+b*deriv f z+κ*f z-(1/4:ℂ)*(z*f z)=0)
    (n : ℕ) :
    (n+1+b)*iteratedDeriv (n+2) f 0+κ*iteratedDeriv (n+1) f 0-
      (n+1)/4*iteratedDeriv n f 0=0 := by
  have he : (fun z : ℂ => z*deriv (deriv f) z+b*deriv f z+κ*f z-(1/4:ℂ)*(z*f z)) =
      fun _ => 0 := funext hode
  have h := congrArg (fun g : ℂ → ℂ => iteratedDeriv (n+1) g 0) he
  have hfa : AnalyticAt ℂ f 0 := hf.analyticAt 0
  have hda : AnalyticAt ℂ (deriv f) 0 := hfa.deriv
  have hdda : AnalyticAt ℂ (deriv (deriv f)) 0 := hda.deriv
  have hs := iteratedDeriv_fun_sub (n := n+1)
    (((analyticAt_id.fun_mul hdda).fun_add ((analyticAt_const (v := b)).fun_mul hda)).fun_add
      ((analyticAt_const (v := κ)).fun_mul hfa)).contDiffAt
    ((analyticAt_const (v := (1/4:ℂ))).fun_mul (analyticAt_id.fun_mul hfa)).contDiffAt
  have ha := iteratedDeriv_fun_add (n := n+1)
    ((analyticAt_id.fun_mul hdda).fun_add ((analyticAt_const (v := b)).fun_mul hda)).contDiffAt
    ((analyticAt_const (v := κ)).fun_mul hfa).contDiffAt
  have ha' := iteratedDeriv_fun_add (n := n+1) (analyticAt_id.fun_mul hdda).contDiffAt
    ((analyticAt_const (v := b)).fun_mul hda).contDiffAt
  simp only [id_eq] at hs ha ha'
  rw [hs,ha,ha'] at h
  simp only [iteratedDeriv_const_mul_field,buchholz_iteratedDeriv_id_mul_zero hdda,buchholz_iteratedDeriv_id_mul_zero hfa,
    iteratedDeriv_const,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,
    ← iteratedDeriv_succ',show n+1+1=n+2 by omega] at h
  linear_combination h

/-- An entire solution of the normalized Whittaker equation vanishes when its initial value
 vanishes and the indicial parameter avoids the nonpositive integers. -/
private lemma buchholz_normalized_ode_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {b κ : ℂ}
    (hb : ∀ n : ℕ, b ≠ -(n:ℂ))
    (hode : ∀ z, z*deriv (deriv f) z+b*deriv f z+κ*f z-(1/4:ℂ)*(z*f z)=0)
    (h0 : f 0=0) : f=0 := by
  have hjet : ∀ n, iteratedDeriv n f 0=0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | _ | n
      · simpa using h0
      · have hz := hode 0
        have hb0 : b ≠ 0 := by simpa using hb 0
        simpa [h0,hb0] using hz
      · have hz := buchholz_normalized_ode_jet hf b κ hode n
        rw [ih n (by omega), ih (n+1) (by omega)] at hz
        have hne : (n:ℂ)+1+b ≠ 0 := by
          intro hh
          exact hb (n+1) (by push_cast; linear_combination hh)
        simpa [hne] using hz
  funext z
  have hs := Complex.hasSum_taylorSeries_of_entire hf 0 z
  simp_rw [hjet, smul_zero] at hs
  exact hs.unique hasSum_zero

/-- Removing the elementary power prefactor from Whittaker M gives the normalized equation. -/
private lemma buchholz_normalized_confluent_ode (κ μ z : ℂ) :
    let H : ℂ → ℂ := fun w => exp (-w/2)*regularizedHGFun {μ-κ+1/2} {2*μ+1} w
    z*deriv (deriv H) z+(2*μ+1)*deriv H z+(κ-z/4)*H z=0 := by
  let a := μ-κ+1/2
  let b := 2*μ+1
  let y : ℂ → ℂ := regularizedHGFun {a} {b}
  let H : ℂ → ℂ := fun w => exp (-w/2)*y w
  change z*deriv (deriv H) z+b*deriv H z+(κ-z/4)*H z=0
  have hy : Differentiable ℂ y := fun w => differentiableAt_regularizedConfluent a b w
  have hφ (w : ℂ) : HasDerivAt (fun t : ℂ => exp (-t/2)) (-(exp (-w/2)/2)) w := by
    apply (((hasDerivAt_id' w).neg.div_const 2).cexp).congr_deriv
    simp only [Pi.neg_apply]
    ring
  have hM : z*deriv (deriv y) z+(b-z)*deriv y z-a*y z=0 := by
    have he := regularizedConfluent_ode_contiguous a b z
    have hd : deriv (deriv y) z=a*((a+1)*regularizedHGFun {a+1+1} {b+1+1} z) := by
      have hfun : deriv y=fun w => a*regularizedHGFun {a+1} {b+1} w :=
        funext (deriv_regularizedConfluent a b)
      rw [hfun,deriv_const_mul_field,deriv_regularizedConfluent]
    rw [hd,show deriv y z=a*regularizedHGFun {a+1} {b+1} z from deriv_regularizedConfluent a b z]
    change z*(a*((a+1)*regularizedHGFun {a+1+1} {b+1+1} z))+
      (b-z)*(a*regularizedHGFun {a+1} {b+1} z)-a*regularizedHGFun {a} {b} z=0
    rw [show a+1+1=a+2 by ring,show b+1+1=b+2 by ring]
    linear_combination a*he
  have hfirst (w : ℂ) : deriv H w=exp (-w/2)*(deriv y w-y w/2) := by
    have hd := (hφ w).fun_mul (hy w).hasDerivAt
    convert hd.deriv using 1
    ring
  have hsecond : deriv (deriv H) z=exp (-z/2)*(deriv (deriv y) z-deriv y z+y z/4) := by
    rw [show deriv H=fun w=>exp (-w/2)*(deriv y w-y w/2) from funext hfirst]
    have hd := (hφ z).fun_mul ((hy.deriv z).hasDerivAt.fun_sub ((hy z).hasDerivAt.div_const 2))
    convert hd.deriv using 1
    ring
  rw [hsecond,hfirst]
  dsimp only [H]
  dsimp only [a,b] at hM ⊢
  linear_combination exp (-z/2)*hM


/-- The entire Buchholz sum and normalized Whittaker M have the same initial value and satisfy
 the same differential equation, so their Taylor series agree. -/
private lemma buchholz_sum_eq_normalized (κ μ z : ℂ)
    (hμ : ∀ k : ℕ, 1+2*μ ≠ -(k:ℂ)) :
    (∑' s, buchholzTerm κ μ s z)=
      exp (-z/2)*regularizedHGFun {μ-κ+1/2} {2*μ+1} z := by
  let S : ℂ → ℂ := fun w => ∑' s, buchholzTerm κ μ s w
  let H : ℂ → ℂ := fun w => exp (-w/2)*regularizedHGFun {μ-κ+1/2} {2*μ+1} w
  let d : ℂ → ℂ := fun w => S w-H w
  have hs := buchholz_sum_differentiable κ μ
  have hh : Differentiable ℂ H := by
    exact ((differentiable_id.neg.div_const 2).cexp).mul
      (fun w => differentiableAt_regularizedConfluent _ _ w)
  have hS0 : S 0=(Gamma (2*μ+1))⁻¹ := by
    dsimp only [S]
    rw [tsum_eq_single 0]
    · simp [buchholzTerm,buchholzC,whittakerTaylorD,whittakerGenD_zero,
        whittakerBesselGenerating,regularizedHGFunCoeff]
    · intro s hs0
      simp [buchholzTerm,buchholzC,zero_pow hs0]
  have hH0 : H 0=(Gamma (2*μ+1))⁻¹ := by
    simp [H,regularizedHGFunCoeff_singleton,poch]
  have hd : deriv d=fun w => deriv S w-deriv H w := by
    funext w
    exact deriv_fun_sub (hs w) (hh w)
  have hdd : deriv (deriv d)=fun w => deriv (deriv S) w-deriv (deriv H) w := by
    rw [hd]
    funext w
    exact deriv_fun_sub (hs.deriv w) (hh.deriv w)
  have hode : ∀ w, w*deriv (deriv d) w+(2*μ+1)*deriv d w+κ*d w-
      (1/4:ℂ)*(w*d w)=0 := by
    intro w
    rw [hdd,hd]
    dsimp only [d]
    have heS := buchholz_sum_ode κ μ w
    have heH := buchholz_normalized_confluent_ode κ μ w
    change w*deriv (deriv H) w+(2*μ+1)*deriv H w+(κ-w/4)*H w=0 at heH
    change w*deriv (deriv S) w+(2*μ+1)*deriv S w+(κ-w/4)*S w=0 at heS
    linear_combination heS-heH
  have hd0 : d 0=0 := by dsimp only [d]; rw [hS0,hH0,sub_self]
  have he := buchholz_normalized_ode_zero (hs.fun_sub hh)
    (b:=2*μ+1) (κ:=κ) (fun n => by simpa only [add_comm] using hμ n) hode hd0
  have hz := congrFun he z
  exact sub_eq_zero.mp hz

/-- The Whittaker–Buchholz expansion of `M_{κ,μ}` in Bessel functions of consecutive orders
(DLMF 13.24.2). The generating-function recurrence determines the sum through the normalized
Whittaker equation, and the principal powers cancel term by term. -/
@[dlmf 13.24.E2]
theorem whittakerM_besselJ_series {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hκ : 0 < κ.re) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ z / Gamma (1 + 2 * μ) =
      (2 : ℂ) ^ (2 * μ) * z ^ (μ + 1 / 2) *
        ∑' s : ℕ, whittakerBesselCoeff μ z s *
          (2 * (κ * z) ^ (1 / 2 : ℂ)) ^ (-(2 * μ + s)) *
          besselJ (2 * μ + s) (2 * (κ * z) ^ (1 / 2 : ℂ)) := by
  have hz0 := slitPlane_ne_zero hz
  have hκ0 : κ ≠ 0 := by intro h; simp [h] at hκ
  have hb := whittakerBessel_series_eq_regularized hκ0 hz0 μ
  have hs := buchholz_sum_eq_normalized κ μ z hμ
  have hs' : exp (-z/2)*regularizedHGFun {μ-κ+1/2} {2*μ+1} z =
      ∑' s : ℕ, whittakerBesselCoeff μ z s/(2:ℂ)^s*
        regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*z)) := by
    simpa only [buchholzTerm,buchholzC_eq] using hs.symm
  rw [← regularizedWhittakerM_eq_div_Gamma hμ]
  unfold regularizedWhittakerM
  rw [show 1+2*μ=2*μ+1 by ring]
  calc exp (-z/2)*z^(μ+1/2)*regularizedHGFun {μ-κ+1/2} {2*μ+1} z =
      z^(μ+1/2)*(exp (-z/2)*regularizedHGFun {μ-κ+1/2} {2*μ+1} z) := by ring
    _ = _ := by rw [hs',← hb]; ring


end DLMF.Confluent
