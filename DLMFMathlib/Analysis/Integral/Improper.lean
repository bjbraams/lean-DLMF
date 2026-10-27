/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonSector

/-!
# Conditionally convergent improper integrals

Tools for improper integrals `lim_{R → ∞} ∫₀^R f` that need not converge absolutely, as they
occur for oscillatory integrands such as `t^{μ-1} sin t` or Hankel-type kernels.

## Main results

* `MeasureTheory.exists_norm_le_of_continuousOn_of_tendsto`: a continuous function on `[a, ∞)`
  with a limit at infinity is bounded there.
* `MeasureTheory.tendsto_abel_of_tendsto_intervalIntegral`: **Abel's theorem for integrals**. If
  `∫₀^R f → L` then the Abel means `∫₀^∞ e^{-εt} f(t) dt` (as improper integrals) tend to `L` as
  `ε → 0⁺`. With `MeasureTheory.eq_of_tendsto_abel` this identifies the value of a convergent
  improper integral with the limit of its exponentially regularized versions.
* `MeasureTheory.tendsto_intervalIntegral_integral_of_dominated`: dominated convergence for
  improper integrals of parametric integrals (Fubini on `[a, R] × α` followed by dominated
  convergence in the parameter).
* `Complex.tendsto_integral_cpow_mul_sin`: the conditionally convergent Mellin transform of the
  sine, `∫₀^∞ u^{μ-1} sin u du = Γ(μ) sin(πμ/2)` for `-1 < re μ < 1`, `μ ≠ 0`.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology Real

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- A function continuous on `[a, ∞)` with a limit at infinity is bounded on `[a, ∞)`. -/
theorem exists_norm_le_of_continuousOn_of_tendsto {F : ℝ → E} {a : ℝ} {L : E}
    (hF : ContinuousOn F (Ici a)) (hL : Tendsto F atTop (𝓝 L)) :
    ∃ C, ∀ x ∈ Ici a, ‖F x‖ ≤ C := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hL.norm.eventually (eventually_le_nhds (lt_add_one ‖L‖)))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := max a T)).exists_bound_of_continuousOn
    (hF.mono Icc_subset_Ici_self)
  refine ⟨max C (‖L‖ + 1), fun x hx => ?_⟩
  by_cases h : x ≤ max a T
  · exact (hC x ⟨hx, h⟩).trans (le_max_left _ _)
  · exact (hT x ((le_max_right _ _).trans (not_le.mp h).le)).trans (le_max_right _ _)

/-- **Abel's theorem for improper integrals.** Let `f` be continuous on `(0, ∞)` and integrable
on every `[0, b]`, with `∫₀^R f → L` as `R → ∞`. If for each `ε > 0` the regularized improper
integral `∫₀^R e^{-εt} f(t) dt` tends to `g ε`, then `g ε → L` as `ε → 0⁺`. -/
theorem tendsto_abel_of_tendsto_intervalIntegral {f : ℝ → E} {L : E}
    (hf : ContinuousOn f (Ioi 0)) (hfi : ∀ b, IntervalIntegrable f volume 0 b)
    (hL : Tendsto (fun R => ∫ t in (0 : ℝ)..R, f t) atTop (𝓝 L)) {g : ℝ → E}
    (hg : ∀ ε > 0, Tendsto (fun R => ∫ t in (0 : ℝ)..R, Real.exp (-(ε * t)) • f t) atTop
      (𝓝 (g ε))) :
    Tendsto g (𝓝[>] 0) (𝓝 L) := by
  set F : ℝ → E := fun t => ∫ s in (0 : ℝ)..t, f s with hFdef
  have hii : ∀ a b, IntervalIntegrable f volume a b := fun a b => (hfi a).symm.trans (hfi b)
  have hFc : Continuous F := intervalIntegral.continuous_primitive hii 0
  obtain ⟨C, hC⟩ := exists_norm_le_of_continuousOn_of_tendsto hFc.continuousOn hL
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (mem_Ici.mpr le_rfl))
  have hFd : ∀ t, 0 < t → HasDerivAt F (f t) t := fun t ht =>
    intervalIntegral.integral_hasDerivAt_right (hii 0 t)
      (hf.stronglyMeasurableAtFilter isOpen_Ioi t ht) (hf.continuousAt (Ioi_mem_nhds ht))
  -- the regularized integral as `ε ∫₀^∞ e^{-εt} F(t) dt`
  have hgε : ∀ ε > 0, g ε = ∫ t in Ioi (0 : ℝ), (ε * Real.exp (-(ε * t))) • F t := by
    intro ε hε
    have hint : IntegrableOn (fun t => (ε * Real.exp (-(ε * t))) • F t) (Ioi 0) := by
      have hexp : IntegrableOn (fun t => ε * C * Real.exp (-ε * t)) (Ioi 0) :=
        (exp_neg_integrableOn_Ioi 0 hε).const_mul (ε * C)
      refine hexp.mono' ((Continuous.smul (by fun_prop) hFc).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have := hC t (le_of_lt ht)
      calc ε * Real.exp (-(ε * t)) * ‖F t‖ ≤ ε * Real.exp (-(ε * t)) * C :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = ε * C * Real.exp (-ε * t) := by ring_nf
    have hlim1 : Tendsto (fun R => Real.exp (-(ε * R)) • F R) atTop (𝓝 0) := by
      have he : Tendsto (fun R => Real.exp (-(ε * R))) atTop (𝓝 0) := by
        have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hε)
        simpa [Function.comp_def] using this
      refine squeeze_zero_norm' ?_ (by simpa using he.mul_const C)
      filter_upwards [eventually_ge_atTop 0] with R hR
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hC R hR) (Real.exp_pos _).le
    have hlim2 := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
    have hibp : ∀ R, 0 ≤ R → ∫ t in (0 : ℝ)..R, Real.exp (-(ε * t)) • f t =
        Real.exp (-(ε * R)) • F R + ∫ t in (0 : ℝ)..R, (ε * Real.exp (-(ε * t))) • F t := by
      intro R hR
      have h := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
        (a := 0) (b := R) (u := fun t => Real.exp (-(ε * t)))
        (u' := fun t => -(ε * Real.exp (-(ε * t)))) (v := F) (v' := f)
        (by fun_prop) hFc.continuousOn
        (fun t _ => by
          have h := ((hasDerivAt_id t).const_mul ε).neg.exp
          refine h.congr_deriv ?_
          simp only [Pi.neg_apply, id, mul_one]; ring)
        (fun t ht => hFd t (by
          rw [min_eq_left hR] at ht; exact ht.1))
        (by apply Continuous.intervalIntegrable; fun_prop) (hfi R)
      have hF0 : F 0 = 0 := by simp [hFdef]
      rw [h, hF0, smul_zero, sub_zero]
      simp only [neg_smul, intervalIntegral.integral_neg, sub_neg_eq_add]
    have := hlim1.add hlim2
    rw [zero_add] at this
    refine tendsto_nhds_unique (hg ε hε) (this.congr' ?_)
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [hibp R hR]; rfl
  -- the substitution `t = v / ε`
  have hsub : ∀ ε > 0, g ε = ∫ v in Ioi (0 : ℝ), Real.exp (-v) • F (ε⁻¹ * v) := by
    intro ε hε
    rw [hgε ε hε]
    have h := integral_comp_mul_left_Ioi (fun v => Real.exp (-v) • F (ε⁻¹ * v)) 0 hε
    simp only [mul_zero] at h
    have h2 : ∀ t, Real.exp (-(ε * t)) • F (ε⁻¹ * (ε * t)) = Real.exp (-(ε * t)) • F t := by
      intro t; rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
    simp only [h2] at h
    simp_rw [mul_smul]
    rw [integral_smul, h, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  have hDCT : Tendsto (fun ε => ∫ v in Ioi (0 : ℝ), Real.exp (-v) • F (ε⁻¹ * v)) (𝓝[>] 0)
      (𝓝 (∫ v in Ioi (0 : ℝ), Real.exp (-v) • L)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun v => Real.exp (-v) * C)
      (Eventually.of_forall fun ε => ?_) ?_ ?_ ?_
    · exact (Continuous.smul (by fun_prop) (hFc.comp (by fun_prop))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hC _ (mul_nonneg (inv_pos.mpr hε).le (le_of_lt hv)))
        (Real.exp_pos _).le
    · exact IntegrableOn.congr_fun ((exp_neg_integrableOn_Ioi 0 one_pos).mul_const C)
        (fun v _ => by simp) measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      refine Tendsto.const_smul (hL.comp ?_) _
      exact tendsto_inv_nhdsGT_zero.atTop_mul_const hv
  rw [integral_smul_const, integral_exp_neg_Ioi_zero, one_smul] at hDCT
  exact hDCT.congr' (eventually_nhdsWithin_of_forall fun ε hε => (hsub ε hε).symm)

/-- Abel's theorem for integrals, in the form of an equality: if `∫₀^R f → L` and the
regularized improper integrals `∫₀^R e^{-εt} f(t) dt` tend to `g ε` with `g ε → M` as
`ε → 0⁺`, then `L = M`. -/
theorem eq_of_tendsto_abel {f : ℝ → E} {L M : E}
    (hf : ContinuousOn f (Ioi 0)) (hfi : ∀ b, IntervalIntegrable f volume 0 b)
    (hL : Tendsto (fun R => ∫ t in (0 : ℝ)..R, f t) atTop (𝓝 L)) {g : ℝ → E}
    (hg : ∀ ε > 0, Tendsto (fun R => ∫ t in (0 : ℝ)..R, Real.exp (-(ε * t)) • f t) atTop
      (𝓝 (g ε))) (hM : Tendsto g (𝓝[>] 0) (𝓝 M)) : L = M :=
  tendsto_nhds_unique (tendsto_abel_of_tendsto_intervalIntegral hf hfi hL hg) hM

/-- Abel's theorem for integrals when the regularized integrands are integrable on `(0, ∞)`:
`∫₀^∞ e^{-εt} f(t) dt → L` as `ε → 0⁺` whenever `∫₀^R f → L`. -/
theorem tendsto_integral_Ioi_exp_neg_mul_smul {f : ℝ → E} {L : E}
    (hf : ContinuousOn f (Ioi 0)) (hfi : ∀ b, IntervalIntegrable f volume 0 b)
    (hL : Tendsto (fun R => ∫ t in (0 : ℝ)..R, f t) atTop (𝓝 L))
    (hint : ∀ ε > 0, IntegrableOn (fun t => Real.exp (-(ε * t)) • f t) (Ioi 0)) :
    Tendsto (fun ε => ∫ t in Ioi (0 : ℝ), Real.exp (-(ε * t)) • f t) (𝓝[>] 0) (𝓝 L) :=
  tendsto_abel_of_tendsto_intervalIntegral hf hfi hL fun ε hε =>
    intervalIntegral_tendsto_integral_Ioi 0 (hint ε hε) tendsto_id

omit [CompleteSpace E] in
/-- **Dominated convergence for improper integrals of parametric integrals.** Suppose that
`(t, s) ↦ K t s` is integrable on `(a, R] × α` for every `R ≥ a`, that the partial integrals
`∫_a^R K t s dt` are dominated by an integrable function of `s` and converge to `g s` for
almost every `s`. Then `∫_a^R (∫ K t s ds) dt → ∫ g s ds`. -/
theorem tendsto_intervalIntegral_integral_of_dominated {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [SFinite ν] {a : ℝ} {K : ℝ → α → E} {g : α → E} {bound : α → ℝ}
    (hK : ∀ R, a ≤ R → Integrable (Function.uncurry K) ((volume.restrict (Ioc a R)).prod ν))
    (hbound : ∀ R, a ≤ R → ∀ᵐ s ∂ν, ‖∫ t in a..R, K t s‖ ≤ bound s)
    (hbi : Integrable bound ν)
    (hlim : ∀ᵐ s ∂ν, Tendsto (fun R => ∫ t in a..R, K t s) atTop (𝓝 (g s))) :
    Tendsto (fun R => ∫ t in a..R, ∫ s, K t s ∂ν) atTop (𝓝 (∫ s, g s ∂ν)) := by
  have hswap : ∀ R, a ≤ R → ∫ t in a..R, ∫ s, K t s ∂ν = ∫ s, (∫ t in a..R, K t s) ∂ν := by
    intro R hR
    simp_rw [intervalIntegral.integral_of_le hR]
    exact integral_integral_swap (hK R hR)
  have hDCT : Tendsto (fun R => ∫ s, (∫ t in a..R, K t s) ∂ν) atTop (𝓝 (∫ s, g s ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbi hlim
    · filter_upwards [eventually_ge_atTop a] with R hR
      simp_rw [intervalIntegral.integral_of_le hR]
      exact (hK R hR).integral_prod_right.aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop a] with R hR
      exact hbound R hR
  refine hDCT.congr' ?_
  filter_upwards [eventually_ge_atTop a] with R hR
  exact (hswap R hR).symm

end MeasureTheory

namespace Complex

open MeasureTheory

/-- `u^{μ-1} sin u = u^μ sinc u` for `μ ≠ 0`, including `u = 0`. -/
private lemma improper_cpow_sub_one_mul_sin {μ : ℂ} (hμ : μ ≠ 0) (u : ℝ) :
    (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ) = (u : ℂ) ^ μ * (Real.sinc u : ℂ) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [zero_cpow hμ]
  · rw [Real.sinc_of_ne_zero hu, cpow_sub _ _ (ofReal_ne_zero.mpr hu), cpow_one]
    push_cast
    field_simp

/-- For `u > 0`, `‖u^{μ-1} sin u‖ ≤ u^{re μ}`. -/
private lemma improper_norm_cpow_sub_one_mul_sin_le {μ : ℂ} (hμ : μ ≠ 0) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)‖ ≤ u ^ μ.re := by
  rw [improper_cpow_sub_one_mul_sin hμ, norm_mul, norm_cpow_eq_rpow_re_of_pos hu, norm_real,
    Real.norm_eq_abs]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hu.le _) (Real.abs_sinc_le_one u)

/-- The Mellin sine integrand is interval integrable when `re μ > -1`. -/
private lemma improper_intervalIntegrable_cpow_sub_one_mul_sin {μ : ℂ} (h0 : -1 < μ.re)
    (hμ : μ ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)) volume a b := by
  simp_rw [improper_cpow_sub_one_mul_sin hμ]
  exact (intervalIntegral.intervalIntegrable_cpow' h0).mul_continuousOn
    (continuous_ofReal.comp Real.continuous_sinc).continuousOn

/-- The improper Mellin sine integral `∫₀^X u^{μ-1} sin u du` converges as `X → ∞` when
`-1 < re μ < 1`. -/
private lemma improper_exists_tendsto_cpow_sub_one_mul_sin {μ : ℂ} (h0 : -1 < μ.re)
    (h1 : μ.re < 1) (hμ : μ ≠ 0) :
    ∃ L, Tendsto (fun X : ℝ => ∫ u in (0 : ℝ)..X, (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ))
      atTop (𝓝 L) := by
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)
  have hfi := improper_intervalIntegrable_cpow_sub_one_mul_sin h0 hμ
  set g : ℝ → ℂ := fun u => (μ - 1) * (u : ℂ) ^ (μ - 1 - 1) * (-(Real.cos u : ℂ))
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt (fun u : ℝ => (u : ℂ) ^ (μ - 1))
      ((μ - 1) * (x : ℂ) ^ (μ - 1 - 1)) x := by
    intro x hx
    have h := ((hasDerivAt_id (x : ℂ)).cpow_const (c := μ - 1)
      (by simpa using ofReal_mem_slitPlane.mpr hx)).comp_ofReal
    simpa using h
  have hgint : IntegrableOn g (Ioi 1) := by
    have hb : IntegrableOn (fun u : ℝ => ‖μ - 1‖ * u ^ (μ.re - 2)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    refine hb.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
      have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
      refine ContinuousAt.continuousWithinAt ?_
      refine (continuousAt_const.mul ?_).mul (by fun_prop)
      exact (continuous_ofReal.continuousAt).cpow continuousAt_const
        (ofReal_mem_slitPlane.mpr hu0)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
      simp only [g, norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
        norm_cpow_eq_rpow_re_of_pos hu0]
      have : |Real.cos u| ≤ 1 := Real.abs_cos_le_one u
      have hre : (μ - 1 - 1).re = μ.re - 2 := by simp; ring
      rw [hre]
      calc ‖μ - 1‖ * u ^ (μ.re - 2) * |Real.cos u| ≤ ‖μ - 1‖ * u ^ (μ.re - 2) * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := mul_one _
  have hibp : ∀ X : ℝ, 1 ≤ X → ∫ u in (0 : ℝ)..X, f u =
      (∫ u in (0 : ℝ)..1, f u) + ((X : ℂ) ^ (μ - 1) * (-(Real.cos X : ℂ)) -
        (1 : ℂ) ^ (μ - 1) * (-(Real.cos 1 : ℂ)) - ∫ u in (1 : ℝ)..X, g u) := by
    intro X hX
    rw [← intervalIntegral.integral_add_adjacent_intervals (hfi 0 1) (hfi 1 X)]
    congr 1
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 1) (b := X)
      (u := fun u : ℝ => (u : ℂ) ^ (μ - 1)) (u' := fun x => (μ - 1) * (x : ℂ) ^ (μ - 1 - 1))
      (v := fun u : ℝ => -(Real.cos u : ℂ)) (v' := fun u => (Real.sin u : ℂ))
      (fun x hx => hderiv x (by
        rw [uIcc_of_le hX] at hx; exact lt_of_lt_of_le one_pos hx.1))
      (fun x _ => by
        have := ((Real.hasDerivAt_cos x).ofReal_comp).neg
        refine this.congr_deriv ?_
        push_cast; ring)
      ?_ ?_
    · simpa [f, g, mul_assoc] using h
    · refine ContinuousOn.intervalIntegrable (fun x hx => ?_)
      rw [uIcc_of_le hX] at hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx.1
      refine ContinuousAt.continuousWithinAt (continuousAt_const.mul ?_)
      exact (continuous_ofReal.continuousAt).cpow continuousAt_const
        (ofReal_mem_slitPlane.mpr hx0)
    · exact (continuous_ofReal.comp Real.continuous_sin).intervalIntegrable _ _
  have hb : Tendsto (fun X : ℝ => (X : ℂ) ^ (μ - 1) * (-(Real.cos X : ℂ))) atTop (𝓝 0) := by
    have hr : Tendsto (fun X : ℝ => X ^ (μ.re - 1)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := 1 - μ.re) (by linarith)
      simpa [neg_sub] using this
    refine squeeze_zero_norm' ?_ hr
    filter_upwards [eventually_gt_atTop 0] with X hX
    rw [norm_mul, norm_neg, norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos hX]
    have : (μ - 1).re = μ.re - 1 := by simp
    rw [this]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hX.le _) (Real.abs_cos_le_one X)
  have hI := intervalIntegral_tendsto_integral_Ioi 1 hgint tendsto_id
  refine ⟨(∫ u in (0 : ℝ)..1, f u) + (0 - (1 : ℂ) ^ (μ - 1) * (-(Real.cos 1 : ℂ)) -
    ∫ u in Ioi 1, g u), ?_⟩
  have := (tendsto_const_nhds (x := ∫ u in (0 : ℝ)..1, f u)).add
    ((hb.sub (tendsto_const_nhds (x := (1 : ℂ) ^ (μ - 1) * (-(Real.cos 1 : ℂ))))).sub hI)
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [hibp X hX]
  rfl

/-- `u ↦ u^s` is continuous at every `u > 0`. -/
private lemma improper_continuousAt_cpow {s : ℂ} {u : ℝ} (hu : 0 < u) :
    ContinuousAt (fun x : ℝ => (x : ℂ) ^ s) u :=
  (continuous_ofReal.continuousAt).cpow continuousAt_const (ofReal_mem_slitPlane.mpr hu)

/-- `u^s e^{-zu}` is integrable on `(0, ∞)` for `re s > -1`, `re z > 0`. -/
private lemma improper_integrableOn_cpow_mul_cexp {s z : ℂ} (hs : -1 < s.re) (hz : 0 < z.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ s * exp (-(z * u))) (Ioi 0) := by
  have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s.re) (p := 1) (b := z.re) hs one_pos hz
  simp only [Real.rpow_one] at hb
  refine hb.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
    exact ((improper_continuousAt_cpow hu).mul (by fun_prop)).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp]
    simp [mul_comm]

/-- The exponentially regularized Mellin sine integral: for `ε > 0`, `re μ > -1`, `μ ≠ 0`,
`∫₀^∞ e^{-εu} u^{μ-1} sin u du = -(i/2) Γ(μ) ((ε - i)^{-μ} - (ε + i)^{-μ})`. -/
theorem integral_exp_neg_mul_cpow_sub_one_mul_sin {μ : ℂ} (h0 : -1 < μ.re) (hμ : μ ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u : ℝ => Real.exp (-(ε * u)) • ((u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)))
      (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), Real.exp (-(ε * u)) • ((u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)) =
      -(I / 2) * Gamma μ * (((ε : ℂ) - I) ^ (-μ) - ((ε : ℂ) + I) ^ (-μ)) := by
  have hmaj := integrableOn_rpow_mul_exp_neg_mul_rpow (s := μ.re) (p := 1) (b := ε) h0 one_pos hε
  simp only [Real.rpow_one] at hmaj
  have hint : IntegrableOn
      (fun u : ℝ => Real.exp (-(ε * u)) • ((u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ))) (Ioi 0) := by
    refine hmaj.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
      have h1 : ContinuousAt (fun u : ℝ => Real.exp (-(ε * u))) u := by fun_prop
      have h2 : ContinuousAt (fun u : ℝ => (Real.sin u : ℂ)) u := by fun_prop
      exact (h1.smul ((improper_continuousAt_cpow hu).mul h2)).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(ε * u)) * ‖(u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)‖
          ≤ Real.exp (-(ε * u)) * u ^ μ.re :=
            mul_le_mul_of_nonneg_left (improper_norm_cpow_sub_one_mul_sin_le hμ hu)
              (Real.exp_pos _).le
        _ = u ^ μ.re * Real.exp (-ε * u) := by ring_nf
  refine ⟨hint, ?_⟩
  set U : ℝ → ℂ := fun x => (Real.exp (-(ε * x)) : ℂ) * (Real.sin x : ℂ) with hUdef
  set U' : ℝ → ℂ := fun x =>
    (Real.exp (-(ε * x)) : ℂ) * ((Real.cos x : ℂ) - ε * Real.sin x) with hU'def
  set V : ℝ → ℂ := fun x => (x : ℂ) ^ μ / μ with hVdef
  set V' : ℝ → ℂ := fun x => (x : ℂ) ^ (μ - 1) with hV'def
  have hU : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt U (U' x) x := by
    intro x _
    have he : HasDerivAt (fun x : ℝ => Real.exp (-(ε * x)))
        (Real.exp (-(ε * x)) * -(ε * 1)) x :=
      ((hasDerivAt_id x).const_mul ε).neg.exp
    have h := (he.ofReal_comp).mul (Real.hasDerivAt_sin x).ofReal_comp
    refine h.congr_deriv ?_
    simp only [hU'def]
    push_cast; ring
  have hV : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt V (V' x) x := by
    intro x hx
    have h := hasDerivAt_ofReal_cpow_const' (ne_of_gt hx) (r := μ - 1)
      (by intro h; apply hμ; linear_combination h)
    simp only [sub_add_cancel] at h
    exact h
  have e1 : ∀ x : ℝ, exp (-(((ε : ℂ) - I) * x)) =
      (Real.exp (-(ε * x)) : ℂ) * ((Real.cos x : ℂ) + (Real.sin x : ℂ) * I) := by
    intro x
    rw [show -(((ε : ℂ) - I) * x) = ((-(ε * x) : ℝ) : ℂ) + (x : ℂ) * I by push_cast; ring,
      Complex.exp_add, ← ofReal_exp, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have e2 : ∀ x : ℝ, exp (-(((ε : ℂ) + I) * x)) =
      (Real.exp (-(ε * x)) : ℂ) * ((Real.cos x : ℂ) - (Real.sin x : ℂ) * I) := by
    intro x
    rw [show -(((ε : ℂ) + I) * x) = ((-(ε * x) : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_add, ← ofReal_exp, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast; ring
  set c1 : ℂ := (1 + I * ε) / 2
  set c2 : ℂ := (1 - I * ε) / 2
  have hdec : ∀ x : ℝ, U' x * V x = (1 / μ) * (c1 * ((x : ℂ) ^ (μ + 1 - 1) *
      exp (-(((ε : ℂ) - I) * x))) + c2 * ((x : ℂ) ^ (μ + 1 - 1) * exp (-(((ε : ℂ) + I) * x)))) := by
    intro x
    rw [e1, e2, add_sub_cancel_right]
    simp only [hU'def, hVdef, c1, c2]
    linear_combination (-((x : ℂ) ^ μ * (Real.exp (-(ε * x)) : ℂ) * ε * (Real.sin x : ℂ) / μ)) *
      I_sq
  have hz1 : 0 < ((ε : ℂ) - I).re := by simpa using hε
  have hz2 : 0 < ((ε : ℂ) + I).re := by simpa using hε
  have hs : -1 < (μ + 1 - 1).re := by simpa using h0
  have hi1 := improper_integrableOn_cpow_mul_cexp hs hz1
  have hi2 := improper_integrableOn_cpow_mul_cexp hs hz2
  have hu'v : IntegrableOn (U' * V) (Ioi 0) := by
    have := ((hi1.const_mul c1).add (hi2.const_mul c2)).const_mul (1 / μ)
    refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, Pi.add_apply, hdec x]
  have huv' : IntegrableOn (U * V') (Ioi 0) := by
    refine hint.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, hUdef, hV'def, Complex.real_smul]
    ring
  have hzero : Tendsto (U * V) (𝓝[>] 0) (𝓝 0) := by
    have hr : Tendsto (fun x : ℝ => x ^ (μ.re + 1) / ‖μ‖) (𝓝[>] 0) (𝓝 0) := by
      have : ContinuousAt (fun x : ℝ => x ^ (μ.re + 1) / ‖μ‖) 0 :=
        (Real.continuousAt_rpow_const 0 _ (Or.inr (by linarith))).div_const _
      have h0' := this.tendsto
      simp only [Real.zero_rpow (by linarith : μ.re + 1 ≠ 0), zero_div] at h0'
      exact h0'.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hr
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    simp only [Pi.mul_apply, hUdef, hVdef, norm_mul, norm_div, norm_real, Real.norm_eq_abs,
      norm_cpow_eq_rpow_re_of_pos hx0, abs_of_pos (Real.exp_pos _)]
    have hsin : |Real.sin x| ≤ x := by
      simpa [abs_of_pos hx0] using Real.abs_sin_le_abs (x := x)
    have hexp : Real.exp (-(ε * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hμ0 : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
    rw [Real.rpow_add hx0, Real.rpow_one]
    have hp : 0 ≤ x ^ μ.re := Real.rpow_nonneg hx0.le _
    calc Real.exp (-(ε * x)) * |Real.sin x| * (x ^ μ.re / ‖μ‖)
        ≤ 1 * x * (x ^ μ.re / ‖μ‖) := by gcongr
      _ = x ^ μ.re * x / ‖μ‖ := by ring
  have hinf : Tendsto (U * V) atTop (𝓝 0) := by
    have hr := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero μ.re ε hε).div_const ‖μ‖
    rw [zero_div] at hr
    refine squeeze_zero_norm' ?_ hr
    filter_upwards [eventually_gt_atTop 0] with x hx0
    simp only [Pi.mul_apply, hUdef, hVdef, norm_mul, norm_div, norm_real, Real.norm_eq_abs,
      norm_cpow_eq_rpow_re_of_pos hx0, abs_of_pos (Real.exp_pos _)]
    have hp : 0 ≤ x ^ μ.re := Real.rpow_nonneg hx0.le _
    calc Real.exp (-(ε * x)) * |Real.sin x| * (x ^ μ.re / ‖μ‖)
        ≤ Real.exp (-(ε * x)) * 1 * (x ^ μ.re / ‖μ‖) := by
          gcongr; exact Real.abs_sin_le_one x
      _ = x ^ μ.re * Real.exp (-ε * x) / ‖μ‖ := by ring_nf
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hU hV huv' hu'v hzero hinf
  have hval : ∫ x in Ioi (0 : ℝ), U' x * V x = (1 / μ) * (c1 * (Gamma (μ + 1) *
      ((ε : ℂ) - I) ^ (-(μ + 1))) + c2 * (Gamma (μ + 1) * ((ε : ℂ) + I) ^ (-(μ + 1)))) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hdec x), integral_const_mul,
      integral_add (hi1.const_mul c1) (hi2.const_mul c2), integral_const_mul, integral_const_mul,
      integral_cpow_mul_cexp_neg_mul_Ioi (by simp; linarith) hz1,
      integral_cpow_mul_cexp_neg_mul_Ioi (by simp; linarith) hz2]
  have hlhs : ∫ u in Ioi (0 : ℝ), Real.exp (-(ε * u)) • ((u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)) =
      ∫ x in Ioi (0 : ℝ), U x * V' x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [hUdef, hV'def, Complex.real_smul]
    ring
  rw [hlhs, hibp, hval, Complex.Gamma_add_one μ hμ]
  have hne1 : (ε : ℂ) - I ≠ 0 := fun h => by simp [h] at hz1
  have hne2 : (ε : ℂ) + I ≠ 0 := fun h => by simp [h] at hz2
  have hA : ((ε : ℂ) - I) ^ (-μ) = ((ε : ℂ) - I) ^ (-(μ + 1)) * ((ε : ℂ) - I) := by
    rw [show -μ = -(μ + 1) + 1 by ring, cpow_add _ _ hne1, cpow_one]
  have hB : ((ε : ℂ) + I) ^ (-μ) = ((ε : ℂ) + I) ^ (-(μ + 1)) * ((ε : ℂ) + I) := by
    rw [show -μ = -(μ + 1) + 1 by ring, cpow_add _ _ hne2, cpow_one]
  rw [hA, hB]
  simp only [c1, c2]
  field_simp
  linear_combination (-(Gamma μ * (((ε : ℂ) - I) ^ (-(μ + 1)) + ((ε : ℂ) + I) ^ (-(μ + 1))))) *
    I_sq

/-- **The Mellin transform of the sine** as a conditionally convergent improper integral:
`∫₀^X u^{μ-1} sin u du → Γ(μ) sin(πμ/2)` as `X → ∞`, for `-1 < re μ < 1` and `μ ≠ 0`.
(For `μ = 0` the limit is `π/2`, Dirichlet's integral.) The proof identifies the limit with the
Abel limit of the regularized integrals `integral_exp_neg_mul_cpow_sub_one_mul_sin`. -/
theorem tendsto_integral_cpow_mul_sin {μ : ℂ} (h0 : -1 < μ.re) (h1 : μ.re < 1) (hμ : μ ≠ 0) :
    Tendsto (fun X : ℝ => ∫ u in (0 : ℝ)..X, (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)) atTop
      (𝓝 (Gamma μ * sin (π * μ / 2))) := by
  obtain ⟨L, hL⟩ := improper_exists_tendsto_cpow_sub_one_mul_sin h0 h1 hμ
  have hf : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ)) (Ioi 0) :=
    fun u hu => ((improper_continuousAt_cpow hu).mul (by fun_prop)).continuousWithinAt
  have hfi := improper_intervalIntegrable_cpow_sub_one_mul_sin h0 hμ 0
  set g : ℝ → ℂ := fun ε =>
    ∫ u in Ioi (0 : ℝ), Real.exp (-(ε * u)) • ((u : ℂ) ^ (μ - 1) * (Real.sin u : ℂ))
  have hg : ∀ ε > 0, Tendsto (fun R => ∫ t in (0 : ℝ)..R,
      Real.exp (-(ε * t)) • ((t : ℂ) ^ (μ - 1) * (Real.sin t : ℂ))) atTop (𝓝 (g ε)) :=
    fun ε hε => intervalIntegral_tendsto_integral_Ioi 0
      (integral_exp_neg_mul_cpow_sub_one_mul_sin h0 hμ hε).1 tendsto_id
  set h : ℝ → ℂ := fun ε => -(I / 2) * Gamma μ * (((ε : ℂ) - I) ^ (-μ) - ((ε : ℂ) + I) ^ (-μ))
  have hc : ContinuousAt h 0 := by
    have hm : ContinuousAt (fun ε : ℝ => ((ε : ℂ) - I) ^ (-μ)) 0 :=
      ((continuous_ofReal.continuousAt).sub continuousAt_const).cpow continuousAt_const
        (by simp [slitPlane])
    have hp : ContinuousAt (fun ε : ℝ => ((ε : ℂ) + I) ^ (-μ)) 0 :=
      ((continuous_ofReal.continuousAt).add continuousAt_const).cpow continuousAt_const
        (by simp [slitPlane])
    exact continuousAt_const.mul (hm.sub hp)
  have h0val : h 0 = Gamma μ * sin (π * μ / 2) := by
    simp only [h, ofReal_zero, zero_sub, zero_add]
    rw [cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero), cpow_def_of_ne_zero I_ne_zero,
      log_neg_I, log_I, Complex.sin]
    rw [show -(↑π / 2) * I * -μ = ↑π * μ / 2 * I by ring,
      show ↑π / 2 * I * -μ = -(↑π * μ / 2) * I by ring]
    ring
  have hM : Tendsto g (𝓝[>] 0) (𝓝 (Gamma μ * sin (π * μ / 2))) := by
    rw [← h0val]
    refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (integral_exp_neg_mul_cpow_sub_one_mul_sin h0 hμ hε).2.symm
  have hLM := MeasureTheory.eq_of_tendsto_abel hf hfi hL hg hM
  rwa [hLM] at hL

end Complex
