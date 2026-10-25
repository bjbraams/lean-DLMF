/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import DLMF.Bessel.WeberSeries
public import DLMF.Bessel.LargeOrder
public import DLMF.Gamma.BetaFunction
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy

/-!
# The product integral `J_μ J_ν` (DLMF 10.9.26)

For `ℜ(μ+ν) > -1`,
`J_μ(z) J_ν(z) = (2/π) ∫₀^{π/2} J_{μ+ν}(2z cos θ) cos((μ-ν)θ) dθ`.

## Method

* `integral_cos_cpow_mul_cos`: the cosine Beta integral DLMF 5.12.5 for complex parameters,
  `∫₀^{π/2} cos^{a-1} t cos(bt) dt = π Γ(a) 2^{-a} / (Γ((a+b+1)/2) Γ((a-b+1)/2))`, `ℜ a > 0`.
  The real case is `DLMF.Gamma.integral_cos_rpow_mul_cos`. It is extended to complex `b`
  (entire in `b`) and then to complex `a` (holomorphic on `ℜ a > 0`) by the identity theorem.
* Expanding `J_{μ+ν}(2z cos θ)` in its series and integrating termwise (dominated convergence)
  gives the product series DLMF 10.8.3 (`besselJ_mul_besselJ`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real Topology Nat Interval

noncomputable section

namespace DLMF.Bessel

/-- Right-hand side of the cosine Beta integral DLMF 5.12.5 with reciprocal Gamma factors. -/
def cosBetaValue (a b : ℂ) : ℂ :=
  π * Gamma a * (2 : ℂ) ^ (-a) * (Gamma ((a + b + 1) / 2))⁻¹ * (Gamma ((a - b + 1) / 2))⁻¹

/-- `cos t ≥ 0` on `Ι 0 (π/2)`. -/
lemma cos_nonneg_of_mem_uIoc {t : ℝ} (ht : t ∈ Ι 0 (π / 2)) : 0 ≤ Real.cos t := by
  rw [uIoc_of_le (by positivity)] at ht
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩

/-- DLMF 5.12.5 for real parameters, in complex form. -/
lemma integral_cos_cpow_mul_cos_ofReal {a b : ℝ} (ha : 0 < a) (hb : |b| < a + 1) :
    ∫ t in (0:ℝ)..(π / 2), ((Real.cos t : ℂ)) ^ ((a : ℂ) - 1) * cos ((b : ℂ) * t) =
      cosBetaValue a b := by
  have hcongr : ∫ t in (0:ℝ)..(π / 2), ((Real.cos t : ℂ)) ^ ((a : ℂ) - 1) * cos ((b : ℂ) * t) =
      ∫ t in (0:ℝ)..(π / 2), ((Real.cos t ^ (a - 1) * Real.cos (b * t) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [ofReal_mul, ofReal_cpow (cos_nonneg_of_mem_uIoc ht), ofReal_cos]
    push_cast; rfl
  rw [hcongr, intervalIntegral.integral_ofReal, DLMF.Gamma.integral_cos_rpow_mul_cos ha hb]
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
  have g2 : 0 < Real.Gamma ((a + b + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have g3 : 0 < Real.Gamma ((a - b + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : (2 : ℂ) ^ (-(a : ℂ)) = (((2 : ℝ) ^ a)⁻¹ : ℝ) := by
    rw [← Real.rpow_neg zero_le_two, ofReal_cpow zero_le_two]; push_cast; rfl
  rw [cosBetaValue, h2, show ((a : ℂ) + b + 1) / 2 = (((a + b + 1) / 2 : ℝ) : ℂ) by push_cast; ring,
    show ((a : ℂ) - b + 1) / 2 = (((a - b + 1) / 2 : ℝ) : ℂ) by push_cast; ring,
    Gamma_ofReal, Gamma_ofReal, Gamma_ofReal]
  have : (2:ℝ) ^ a ≠ 0 := by positivity
  push_cast
  field_simp

/-- `‖cos w‖ ≤ exp ‖w‖`. -/
lemma norm_cos_le_exp_norm (w : ℂ) : ‖cos w‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.cos]
  have h1 : ‖exp (w * I)‖ ≤ Real.exp ‖w‖ := by
    rw [norm_exp]; exact Real.exp_le_exp.2 ((re_le_norm _).trans (by simp))
  have h2 : ‖exp (-w * I)‖ ≤ Real.exp ‖w‖ := by
    rw [norm_exp]; exact Real.exp_le_exp.2 ((re_le_norm _).trans (by simp))
  rw [norm_div, Complex.norm_ofNat]
  have := norm_add_le (exp (w * I)) (exp (-w * I))
  linarith

/-- `‖x^s‖ ≤ x^{ℜ s}` for real `x ≥ 0`. -/
lemma norm_ofReal_cpow_le {x : ℝ} (hx : 0 ≤ x) (s : ℂ) : ‖(x : ℂ) ^ s‖ ≤ x ^ s.re := by
  rcases hx.lt_or_eq with hx | rfl
  · rw [norm_cpow_eq_rpow_re_of_pos hx]
  · by_cases hs : s = 0
    · simp [hs]
    · rw [ofReal_zero, zero_cpow hs, norm_zero]
      exact Real.rpow_nonneg le_rfl _

/-- Real points `c + 1/(n+1)` accumulate at `c`. -/
lemma frequently_of_forall_nat_add {c : ℝ} {P : ℂ → Prop}
    (hP : ∀ n : ℕ, P ((c + 1 / ((n:ℝ) + 1) : ℝ))) :
    ∃ᶠ z in 𝓝[≠] (c : ℂ), P z := by
  have hu : Tendsto (fun n : ℕ => ((c + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (c : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add c
      rw [add_zero] at this
      have h2 := (continuous_ofReal.tendsto _).comp this
      simpa [Function.comp_def] using h2
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have h' : (c + 1 / ((n:ℝ) + 1) : ℝ) = c := by exact_mod_cast h
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
  exact hu.frequently (Frequently.of_forall hP)

/-- `cos^{ℜ s}` is integrable on `[0, π/2]` for `ℜ s > -1`. -/
lemma intervalIntegrable_norm_cos_cpow {s : ℂ} (hs : -1 < s.re) :
    IntervalIntegrable (fun t : ℝ => Real.cos t ^ s.re) volume 0 (π / 2) :=
  DLMF.Gamma.intervalIntegrable_cos_rpow hs

/-- The cosine Beta integral is entire in `b`. -/
lemma differentiable_cosBeta_integral_right (a : ℂ) (ha : 0 < a.re) :
    Differentiable ℂ fun b : ℂ =>
      ∫ t in (0:ℝ)..(π / 2), ((Real.cos t : ℂ)) ^ (a - 1) * cos (b * t) := by
  have hr : -1 < (a - 1).re := by simp; linarith
  have h := Complex.differentiableOn_intervalIntegral_of_locally_dominated (U := univ)
    (Φ := fun b (t : ℝ) => ((Real.cos t : ℂ)) ^ (a - 1) * cos (b * t)) isOpen_univ
    (ν := volume) 0 (π / 2)
    (fun b _ => (Measurable.aestronglyMeasurable (by fun_prop)))
    (Eventually.of_forall fun t => (by fun_prop : Differentiable ℂ fun b : ℂ =>
      ((Real.cos t : ℂ)) ^ (a - 1) * cos (b * t)).differentiableOn)
    (fun b0 _ => ⟨Metric.ball b0 1, Metric.ball_mem_nhds _ one_pos,
      fun t => Real.cos t ^ (a - 1).re * Real.exp ((‖b0‖ + 1) * (π / 2)),
      ((intervalIntegrable_norm_cos_cpow hr).mul_const _).def', by
        refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun t ht y hy => ?_)
        have hc := cos_nonneg_of_mem_uIoc ht
        rw [norm_mul]
        refine mul_le_mul (norm_ofReal_cpow_le hc _) ((norm_cos_le_exp_norm _).trans ?_)
          (norm_nonneg _) (Real.rpow_nonneg hc _)
        rw [Real.exp_le_exp, norm_mul, norm_real, Real.norm_eq_abs]
        rw [uIoc_of_le (by positivity)] at ht
        have h1 : |t| ≤ π / 2 := by rw [abs_of_pos ht.1]; exact ht.2
        have h2 : ‖y‖ ≤ ‖b0‖ + 1 := by
          have := norm_le_norm_add_norm_sub' y b0
          rw [Metric.mem_ball, dist_eq_norm] at hy; linarith
        exact mul_le_mul h2 h1 (abs_nonneg _) (by positivity)⟩)
  exact fun b => (h b (mem_univ b)).differentiableAt (isOpen_univ.mem_nhds (mem_univ b))

/-- The cosine Beta value is entire in `b`. -/
lemma differentiable_cosBetaValue_right (a : ℂ) : Differentiable ℂ fun b => cosBetaValue a b := by
  unfold cosBetaValue
  have hG := differentiable_one_div_Gamma
  exact ((differentiable_const _).mul ((hG.comp (by fun_prop)))).mul (hG.comp (by fun_prop))

/-- DLMF 5.12.5 for real `a > 0` and complex `b`. -/
lemma integral_cos_cpow_mul_cos_ofReal_left {a : ℝ} (ha : 0 < a) (b : ℂ) :
    ∫ t in (0:ℝ)..(π / 2), ((Real.cos t : ℂ)) ^ ((a : ℂ) - 1) * cos (b * t) =
      cosBetaValue a b := by
  have hf := analyticOnNhd_univ_iff_differentiable.2
    (differentiable_cosBeta_integral_right (a : ℂ) (by simpa using ha))
  have hg := analyticOnNhd_univ_iff_differentiable.2 (differentiable_cosBetaValue_right (a : ℂ))
  refine hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_univ (mem_univ ((0:ℝ):ℂ))
    (frequently_of_forall_nat_add fun n => ?_) (mem_univ b)
  apply integral_cos_cpow_mul_cos_ofReal ha
  have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
  have : 1 / ((n:ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [zero_add, abs_of_pos (by assumption)]
  linarith

/-- Almost every point of `Ι 0 (π/2)` lies in the open interval. -/
lemma ae_ne_pi_div_two : ∀ᵐ t ∂(volume.restrict (Ι 0 (π / 2))), t ∈ Ioo 0 (π / 2) := by
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ π / 2 :=
    compl_mem_ae_iff.2 (measure_singleton (π / 2))
  filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem measurableSet_uIoc] with t ht ht'
  rw [uIoc_of_le (by positivity)] at ht'
  exact ⟨ht'.1, lt_of_le_of_ne ht'.2 ht⟩

/-- `cos t > 0` on `(0, π/2)`. -/
lemma cos_pos_of_mem_Ioo {t : ℝ} (ht : t ∈ Ioo 0 (π / 2)) : 0 < Real.cos t :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩

/-- The cosine Beta integral is holomorphic in `a` on `ℜ a > 0`. -/
lemma differentiableOn_cosBeta_integral_left (b : ℂ) :
    DifferentiableOn ℂ (fun a : ℂ =>
      ∫ t in (0:ℝ)..(π / 2), ((Real.cos t : ℂ)) ^ (a - 1) * cos (b * t)) {a | 0 < a.re} := by
  have hU : IsOpen {a : ℂ | 0 < a.re} := isOpen_lt continuous_const continuous_re
  refine Complex.differentiableOn_intervalIntegral_of_locally_dominated
    (Φ := fun a (t : ℝ) => ((Real.cos t : ℂ)) ^ (a - 1) * cos (b * t)) hU
    (ν := volume) 0 (π / 2)
    (fun a _ => (Measurable.aestronglyMeasurable (by fun_prop))) ?_ ?_
  · filter_upwards [ae_ne_pi_div_two] with t ht
    have hc : (Real.cos t : ℂ) ≠ 0 := ofReal_ne_zero.2 (cos_pos_of_mem_Ioo ht).ne'
    intro a _
    exact (((differentiableAt_id.sub_const 1).const_cpow (Or.inl hc)).mul_const
      _).differentiableWithinAt
  · intro a0 ha0
    simp only [mem_ofPred_eq] at ha0
    refine ⟨Metric.ball a0 (a0.re / 2), Metric.ball_mem_nhds _ (by linarith),
      fun t => Real.cos t ^ (a0.re / 2 - 1) * Real.exp (‖b‖ * (π / 2)),
      ((DLMF.Gamma.intervalIntegrable_cos_rpow (by linarith)).mul_const _).def', ?_⟩
    filter_upwards [ae_ne_pi_div_two] with t ht y hy
    have hc := cos_pos_of_mem_Ioo ht
    have hc1 : Real.cos t ≤ 1 := Real.cos_le_one t
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hc]
    refine mul_le_mul ?_ ((norm_cos_le_exp_norm _).trans ?_) (norm_nonneg _)
      (Real.rpow_nonneg hc.le _)
    · refine Real.rpow_le_rpow_of_exponent_ge hc hc1 ?_
      rw [Metric.mem_ball, dist_eq_norm] at hy
      have := abs_re_le_norm (y - a0)
      rw [sub_re] at this
      have := neg_abs_le (y.re - a0.re)
      simp only [sub_re, one_re]; linarith
    · rw [Real.exp_le_exp, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      exact mul_le_mul_of_nonneg_left ht.2.le (norm_nonneg _)

/-- The cosine Beta value is holomorphic in `a` on `ℜ a > 0`. -/
lemma differentiableOn_cosBetaValue_left (b : ℂ) :
    DifferentiableOn ℂ (fun a => cosBetaValue a b) {a | 0 < a.re} := by
  intro a ha
  simp only [mem_ofPred_eq] at ha
  have hG : DifferentiableAt ℂ Gamma a := differentiableAt_Gamma a fun m h => by
    have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hI := differentiable_one_div_Gamma
  unfold cosBetaValue
  refine DifferentiableAt.differentiableWithinAt ?_
  have h2 : DifferentiableAt ℂ (fun a : ℂ => (2 : ℂ) ^ (-a)) a :=
    (differentiableAt_id.neg).const_cpow (Or.inl two_ne_zero)
  exact ((((differentiableAt_const _).mul hG).mul h2).mul ((hI.comp (by fun_prop)) a)).mul
    ((hI.comp (by fun_prop)) a)

/-- **Cosine Beta integral** (DLMF 5.12.5) for complex parameters:
`∫₀^{π/2} cos^{a-1} t cos(bt) dt = π Γ(a) / (2^a Γ((a+b+1)/2) Γ((a-b+1)/2))` for `ℜ a > 0`
and all complex `b`. -/
theorem integral_cos_cpow_mul_cos {a : ℂ} (ha : 0 < a.re) (b : ℂ) :
    ∫ t in (0:ℝ)..(π / 2), ((Real.cos t : ℂ)) ^ (a - 1) * cos (b * t) = cosBetaValue a b := by
  have hU : IsOpen {a : ℂ | 0 < a.re} := isOpen_lt continuous_const continuous_re
  have hf := (differentiableOn_cosBeta_integral_left b).analyticOnNhd hU
  have hg := (differentiableOn_cosBetaValue_left b).analyticOnNhd hU
  have h1 : ((1:ℝ) : ℂ) ∈ {a : ℂ | 0 < a.re} := by simp
  refine hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected h1
    (frequently_of_forall_nat_add fun n => ?_) ha
  exact integral_cos_cpow_mul_cos_ofReal_left (by positivity) b

open DLMF.Hypergeometric in
/-- `(r z)^s = r^s z^s` for real `r > 0`. -/
lemma ofReal_mul_cpow_of_pos {r : ℝ} (hr : 0 < r) (z s : ℂ) :
    ((r : ℂ) * z) ^ s = (r : ℂ) ^ s * z ^ s := by
  rcases eq_or_ne z 0 with rfl | hz
  · by_cases hs : s = 0
    · simp [hs]
    · simp [zero_cpow hs]
  · have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
    rw [cpow_def_of_ne_zero (mul_ne_zero hr' hz), cpow_def_of_ne_zero hr', cpow_def_of_ne_zero hz,
      log_ofReal_mul hr hz, ← exp_add, ← ofReal_log hr.le]
    ring_nf

/-- A point of `Ι 0 (π/2)` other than `π/2` lies in `(0, π/2)`. -/
lemma mem_Ioo_of_mem_uIoc {t : ℝ} (ht : t ∈ Ι 0 (π / 2)) (h : t ≠ π / 2) : t ∈ Ioo 0 (π / 2) := by
  rw [uIoc_of_le (by positivity)] at ht
  exact ⟨ht.1, lt_of_le_of_ne ht.2 h⟩

/-- Termwise expansion behind the product integral. -/
lemma hasSum_besselJ_cos_integrand (s b z : ℂ) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    HasSum (fun k : ℕ => z ^ s * ((-z ^ 2) ^ k / k ! * (Gamma (s + 1 + k))⁻¹) *
        (((Real.cos θ : ℂ)) ^ ((s + 2 * k + 1) - 1) * cos (b * θ)))
      (besselJ s (2 * z * Real.cos θ) * cos (b * θ)) := by
  have hc := cos_pos_of_mem_Ioo hθ
  have hc0 : (Real.cos θ : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
  set c : ℂ := (Real.cos θ : ℂ)
  have h := ((summable_regularized0F1_term (s + 1) (-z ^ 2 * c ^ 2)).hasSum).mul_left
    (c ^ s * z ^ s * cos (b * θ))
  rw [besselJ_eq_regularized, regularized0F1_eq_tsum,
    show 2 * z * c / 2 = (Real.cos θ : ℂ) * z by ring, ofReal_mul_cpow_of_pos hc,
    show -((2 * z * c) ^ 2 / 4) = -z ^ 2 * c ^ 2 by ring]
  convert h using 1
  · funext k
    rw [show s + 2 * (k : ℂ) + 1 - 1 = s + ((2 * k : ℕ) : ℂ) by push_cast; ring, cpow_add _ _ hc0,
      cpow_natCast, mul_pow, ← pow_mul]
    ring
  · ring

open DLMF.Hypergeometric in
/-- **Product integral** (DLMF 10.9.26):
`J_μ(z) J_ν(z) = (2/π) ∫₀^{π/2} J_{μ+ν}(2z cos θ) cos((μ-ν)θ) dθ` for `ℜ(μ+ν) > -1`. -/
@[dlmf 10.9.E26]
theorem besselJ_mul_besselJ_eq_integral (μ ν : ℂ) (hμν : -1 < (μ + ν).re) {z : ℂ}
    (hz : z ∈ slitPlane) :
    besselJ μ z * besselJ ν z =
      2 / π * ∫ θ in (0:ℝ)..(π / 2), besselJ (μ + ν) (2 * z * Real.cos θ) * cos ((μ - ν) * θ) := by
  set s := μ + ν with hs
  set b := μ - ν with hb
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, a = fun k => (-z ^ 2) ^ k / k ! * (Gamma (s + 1 + k))⁻¹ :=
    ⟨_, rfl⟩
  have hsa : Summable fun k => ‖a k‖ := by
    rw [ha]; exact summable_norm_iff.mpr (summable_regularized0F1_term (s + 1) _)
  set G : ℝ → ℝ := fun θ => ‖z ^ s‖ * (Real.cos θ ^ s.re * Real.exp (‖b‖ * (π / 2))) with hG
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ π / 2 := compl_mem_ae_iff.2 (measure_singleton _)
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := π / 2)
    (F := fun (k : ℕ) (θ : ℝ) => z ^ s * a k *
      (((Real.cos θ : ℂ)) ^ ((s + 2 * k + 1) - 1) * cos (b * θ)))
    (f := fun θ : ℝ => besselJ s (2 * z * Real.cos θ) * cos (b * θ))
    (fun k θ => ‖a k‖ * G θ)
    (fun k => Measurable.aestronglyMeasurable (by fun_prop))
    (fun k => by
      filter_upwards [hne] with θ hθ hθ'
      have ht := mem_Ioo_of_mem_uIoc hθ' hθ
      have hc := cos_pos_of_mem_Ioo ht
      rw [norm_mul, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hc, hG]
      have h1 : Real.cos θ ^ (s + 2 * k + 1 - 1).re ≤ Real.cos θ ^ s.re :=
        Real.rpow_le_rpow_of_exponent_ge hc (Real.cos_le_one θ) (by simp)
      have h2 : ‖cos (b * θ)‖ ≤ Real.exp (‖b‖ * (π / 2)) := by
        refine (norm_cos_le_exp_norm _).trans ?_
        rw [Real.exp_le_exp, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
        exact mul_le_mul_of_nonneg_left ht.2.le (norm_nonneg _)
      calc ‖z ^ s‖ * ‖a k‖ * (Real.cos θ ^ (s + 2 * k + 1 - 1).re * ‖cos (b * θ)‖)
          ≤ ‖z ^ s‖ * ‖a k‖ * (Real.cos θ ^ s.re * Real.exp (‖b‖ * (π / 2))) := by
            gcongr
        _ = _ := by ring)
    (Eventually.of_forall fun θ _ => hsa.mul_right _)
    (by
      simp_rw [tsum_mul_right]
      exact (((DLMF.Gamma.intervalIntegrable_cos_rpow hμν).mul_const _).const_mul _).const_mul _)
    (by
      filter_upwards [hne] with θ hθ hθ'
      rw [ha]
      exact hasSum_besselJ_cos_integrand s b z (mem_Ioo_of_mem_uIoc hθ' hθ))
  have hterm (k : ℕ) : ∫ θ in (0:ℝ)..(π / 2), z ^ s * a k *
      (((Real.cos θ : ℂ)) ^ ((s + 2 * k + 1) - 1) * cos (b * θ)) =
      z ^ s * a k * cosBetaValue (s + 2 * k + 1) b := by
    rw [intervalIntegral.integral_const_mul, integral_cos_cpow_mul_cos (by simp; linarith)]
  simp only [hterm] at hint
  rw [besselJ_mul_besselJ μ ν hz]
  refine (((hint.mul_left (2 / π : ℂ))).tsum_eq.symm.trans ?_).symm
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : 0 < (s + k + 1).re := by simp; linarith
  have hp : Gamma (s + 2 * k + 1) = poch (s + k + 1) k * Gamma (s + 1 + k) := by
    have h := Complex.Gamma_add_nat_div_Gamma_eq (n := k) (s + k + 1) fun m h => by
      have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
    have hG : Gamma (s + k + 1) ≠ 0 := Gamma_ne_zero_of_re_pos hpos
    rw [div_eq_iff hG] at h
    rw [show s + 2 * (k : ℂ) + 1 = s + k + 1 + k by ring, h,
      show s + 1 + (k : ℂ) = s + k + 1 by ring]
  have h2 : (2 : ℂ) ^ (-(s + 2 * k + 1)) = ((2 : ℂ) ^ s)⁻¹ * ((2 : ℂ) ^ (2 * k + 1))⁻¹ := by
    rw [cpow_neg, show s + 2 * (k : ℂ) + 1 = s + ((2 * k + 1 : ℕ) : ℂ) by push_cast; ring,
      cpow_add _ _ two_ne_zero, cpow_natCast, mul_inv]
  have hz2 : (z / 2) ^ s = ((2 : ℂ) ^ s)⁻¹ * z ^ s := by
    rw [show z / 2 = ((1 / 2 : ℝ) : ℂ) * z by push_cast; ring, ofReal_mul_cpow_of_pos (by norm_num),
      show ((1 / 2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ by push_cast; ring,
      inv_cpow _ _ (by simp [Real.pi_pos.ne])]
  have e1 : (s + 2 * k + 1 + b + 1) / 2 = μ + k + 1 := by rw [hs, hb]; ring
  have e2 : (s + 2 * k + 1 - b + 1) / 2 = ν + k + 1 := by rw [hs, hb]; ring
  have h4 : (-(z ^ 2 / 4)) ^ k = (-z ^ 2) ^ k / ((2 : ℂ) ^ (2 * k)) := by
    rw [pow_mul, ← div_pow]; congr 1; ring
  rw [ha, cosBetaValue, e1, e2, hp, h2, hz2, h4, pow_succ (2 : ℂ) (2 * k),
    (show μ + ν + (k : ℂ) + 1 = s + k + 1 by rw [hs])]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hG2 : Gamma (s + 1 + k) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  field_simp

/-! ### Neumann-type series of Bessel products -/

/-- `cos(kπ) = (-1)ᵏ` in `ℂ`. -/
private lemma cos_nat_mul_pi_complex (k : ℕ) : cos ((k : ℂ) * π) = (-1) ^ k := by
  rw [← ofReal_natCast, ← ofReal_mul, ← ofReal_cos, Real.cos_nat_mul_pi]; push_cast; rfl

/-- `sin((2k+1)π/2) = (-1)ᵏ`. -/
private lemma sin_odd_mul_pi_div_two (k : ℕ) :
    sin (((2 * k + 1 : ℕ) : ℂ) * ((π / 2 : ℝ) : ℂ)) = (-1) ^ k := by
  rw [show ((2 * k + 1 : ℕ) : ℂ) * ((π / 2 : ℝ) : ℂ) = (k : ℂ) * π + π / 2 by push_cast; ring,
    sin_add_pi_div_two, cos_nat_mul_pi_complex]

/-- `cos((2k+2)π/2) = (-1)ᵏ⁺¹`. -/
private lemma cos_even_mul_pi_div_two (k : ℕ) :
    cos (((2 * k + 2 : ℕ) : ℂ) * ((π / 2 : ℝ) : ℂ)) = (-1) ^ (k + 1) := by
  rw [show ((2 * k + 2 : ℕ) : ℂ) * ((π / 2 : ℝ) : ℂ) = ((k + 1 : ℕ) : ℂ) * π by push_cast; ring,
    cos_nat_mul_pi_complex]

/-- `sin(π/2) = 1` in `ℂ`. -/
private lemma sin_pi_div_two_complex : sin ((π / 2 : ℝ) : ℂ) = 1 := by
  rw [← ofReal_sin, Real.sin_pi_div_two]; simp

/-- `sin x = 2 ∑ₖ (-1)ᵏ J_{2k+1}(x)` (DLMF 10.12.3 at `θ = π/2`). -/
lemma hasSum_neg_one_pow_besselJ_odd (x : ℂ) :
    HasSum (fun k : ℕ => (-1) ^ k * besselJ (2 * k + 1 : ℕ) x) (sin x / 2) := by
  have h := (hasSum_besselJ_sin x (π / 2)).div_const 2
  rw [sin_pi_div_two_complex, mul_one] at h
  convert h using 1
  funext k
  rw [sin_odd_mul_pi_div_two]
  ring

/-- `cos x = J₀(x) + 2 ∑_{k≥1} (-1)ᵏ J_{2k}(x)` (DLMF 10.12.2 at `θ = π/2`). -/
lemma hasSum_neg_one_pow_besselJ_even (x : ℂ) :
    HasSum (fun k : ℕ => (if k = 0 then 1/2 else 1) * (-1) ^ k * besselJ (2 * k : ℕ) x)
      (cos x / 2) := by
  refine (hasSum_nat_add_iff' 1).mp ?_
  have h := (hasSum_besselJ_cos x (π / 2)).div_const 2
  rw [sin_pi_div_two_complex, mul_one] at h
  convert h using 1
  · funext k
    rw [cos_even_mul_pi_div_two, ite_eq_right_iff.2 (fun h => absurd h (Nat.succ_ne_zero k)),
      show 2 * (k + 1) = 2 * k + 2 by ring]
    ring
  · simp
    ring

/-- `|J_n(w)| ≤ (|w|/2)ⁿ e^{|w|²/4} / n!`. -/
lemma norm_besselJ_nat_le (n : ℕ) (w : ℂ) :
    ‖besselJ n w‖ ≤ (‖w‖ / 2) ^ n * Real.exp (‖w‖ ^ 2 / 4) / n ! := by
  have h := norm_besselJ_le (ν := (n : ℝ)) (Nat.cast_nonneg n) w
  rw [show ((n : ℝ) : ℂ) = (n : ℂ) by norm_cast, cpow_natCast, norm_pow, norm_div,
    Complex.norm_ofNat, Real.Gamma_nat_eq_factorial] at h
  exact h

/-- `θ ↦ J_n(z cos θ)` is continuous. -/
lemma continuous_besselJ_nat_comp (n : ℕ) (z : ℂ) :
    Continuous fun θ : ℝ => besselJ (n : ℂ) (z * Real.cos θ) := by
  have h : Continuous (besselJ (n : ℂ)) := by
    have := (analyticOnNhd_besselJ_int (n : ℤ)).continuousOn
    rw [continuousOn_univ] at this
    simpa using this
  exact h.comp (by fun_prop)

/-- Neumann-type series of Bessel products with half-integer offsets, summed under the
product integral. -/
theorem hasSum_besselJ_products_integral (p q ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => p*(-1)^k*besselJ (k-ν/2+1/2) (z/2)*besselJ (k+ν/2+1/2) (z/2) +
        q*(if k=0 then 1/2 else 1)*(-1)^k*besselJ (k-ν/2) (z/2)*besselJ (k+ν/2) (z/2))
      (2 / π * ∫ θ in (0:ℝ)..(π / 2),
        (p / 2 * sin (z * Real.cos θ) + q / 2 * cos (z * Real.cos θ)) * cos (ν * θ)) := by
  have hz2 : z / 2 ∈ slitPlane := div_two_mem_slitPlane hz
  have hprod (k : ℕ) (α β : ℂ) (n : ℕ) (hαβ : α + β = n) (hβα : α - β = -ν) :
      besselJ α (z / 2) * besselJ β (z / 2) =
        2 / π * ∫ θ in (0:ℝ)..(π / 2), besselJ (n : ℂ) (z * Real.cos θ) * cos (ν * θ) := by
    rw [besselJ_mul_besselJ_eq_integral α β (by
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      rw [hαβ]; simp only [natCast_re]; linarith) hz2]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [hαβ, hβα, show 2 * (z / 2) = z by ring, neg_mul, cos_neg]
  set ε : ℕ → ℂ := fun k => if k = 0 then 1/2 else 1 with hε
  set F : ℕ → ℝ → ℂ := fun k θ => (p * (-1) ^ k * besselJ (2 * k + 1 : ℕ) (z * Real.cos θ) +
      q * ε k * (-1) ^ k * besselJ (2 * k : ℕ) (z * Real.cos θ)) * cos (ν * θ) with hF
  have hterm (k : ℕ) : p*(-1)^k*besselJ (k-ν/2+1/2) (z/2)*besselJ (k+ν/2+1/2) (z/2) +
      q*ε k*(-1)^k*besselJ (k-ν/2) (z/2)*besselJ (k+ν/2) (z/2) =
      2 / π * ∫ θ in (0:ℝ)..(π / 2), F k θ := by
    rw [mul_assoc (p * _), mul_assoc (q * _ * _),
      hprod k _ _ (2 * k + 1) (by push_cast; ring) (by ring),
      hprod k _ _ (2 * k) (by push_cast; ring) (by ring)]
    have h1 : IntervalIntegrable (fun θ : ℝ => besselJ (2 * k + 1 : ℕ) (z * Real.cos θ) *
        cos (ν * θ)) volume 0 (π / 2) :=
      ((continuous_besselJ_nat_comp (2 * k + 1) z).mul (by fun_prop)).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun θ : ℝ => besselJ (2 * k : ℕ) (z * Real.cos θ) *
        cos (ν * θ)) volume 0 (π / 2) :=
      ((continuous_besselJ_nat_comp (2 * k) z).mul (by fun_prop)).intervalIntegrable _ _
    have hF' : (fun θ => F k θ) = fun θ => p * (-1) ^ k *
        (besselJ (2 * k + 1 : ℕ) (z * Real.cos θ) * cos (ν * θ)) +
        q * ε k * (-1) ^ k * (besselJ (2 * k : ℕ) (z * Real.cos θ) * cos (ν * θ)) := by
      funext θ; simp only [hF]; ring
    rw [hF', intervalIntegral.integral_add (h1.const_mul _) (h2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  have hfun : (fun k : ℕ => p*(-1)^k*besselJ (k-ν/2+1/2) (z/2)*besselJ (k+ν/2+1/2) (z/2) +
        q*(if k=0 then 1/2 else 1)*(-1)^k*besselJ (k-ν/2) (z/2)*besselJ (k+ν/2) (z/2)) =
      fun k => 2 / π * ∫ θ in (0:ℝ)..(π / 2), F k θ := funext hterm
  rw [hfun]
  refine HasSum.mul_left _ ?_
  set R := ‖z‖ / 2
  set E := Real.exp (‖z‖ ^ 2 / 4) * Real.exp (‖ν‖ * (π / 2))
  have hbJ (n : ℕ) (θ : ℝ) : ‖besselJ (n : ℂ) (z * Real.cos θ)‖ ≤
      R ^ n * Real.exp (‖z‖ ^ 2 / 4) / n ! := by
    refine (norm_besselJ_nat_le n _).trans ?_
    have hw : ‖z * (Real.cos θ : ℂ)‖ ≤ ‖z‖ := by
      rw [norm_mul, norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one θ)
    have hw' : ‖z * (Real.cos θ : ℂ)‖ / 2 ≤ R := by simp only [R]; linarith
    gcongr
  have hcos (θ : ℝ) (hθ : θ ∈ Ι 0 (π / 2)) : ‖cos (ν * θ)‖ ≤ Real.exp (‖ν‖ * (π / 2)) := by
    refine (norm_cos_le_exp_norm _).trans ?_
    rw [uIoc_of_le (by positivity)] at hθ
    rw [Real.exp_le_exp, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hθ.1]
    exact mul_le_mul_of_nonneg_left hθ.2 (norm_nonneg _)
  have hε1 (k : ℕ) : ‖ε k‖ ≤ 1 := by
    simp only [hε]; split_ifs <;> norm_num
  have hfact (k : ℕ) (m : ℕ) (hm : k ≤ m) : (1 : ℝ) / m ! ≤ 1 / k ! := by
    gcongr
  set B : ℕ → ℝ := fun k => (‖p‖ * R + ‖q‖) * ((R ^ 2) ^ k / k !) * E with hB
  have hint := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := π / 2) (F := F)
    (f := fun θ => (p / 2 * sin (z * Real.cos θ) + q / 2 * cos (z * Real.cos θ)) * cos (ν * θ))
    (fun k _ => B k)
    (fun k => ((by
      simp only [hF]
      exact ((((continuous_const.mul (continuous_besselJ_nat_comp _ z))).add
        (continuous_const.mul (continuous_besselJ_nat_comp _ z))).mul (by fun_prop)) :
        Continuous (F k))).aestronglyMeasurable)
    (fun k => Eventually.of_forall fun θ hθ => by
      simp only [hF, hB]
      have hR : 0 ≤ R := by positivity
      have hk1 := hbJ (2 * k + 1) θ
      have hk0 := hbJ (2 * k) θ
      have hf1 := hfact k (2 * k + 1) (by omega)
      have hf0 := hfact k (2 * k) (by omega)
      rw [norm_mul]
      have H : ‖p * (-1) ^ k * besselJ (2 * k + 1 : ℕ) (z * Real.cos θ) +
          q * ε k * (-1) ^ k * besselJ (2 * k : ℕ) (z * Real.cos θ)‖ ≤
          (‖p‖ * R + ‖q‖) * ((R ^ 2) ^ k / k !) * Real.exp (‖z‖ ^ 2 / 4) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
          one_pow, mul_one, mul_one]
        have hRk : R ^ (2 * k + 1) = R * (R ^ 2) ^ k := by rw [pow_succ, pow_mul, mul_comm]
        have hRk' : R ^ (2 * k) = (R ^ 2) ^ k := pow_mul R 2 k
        have e1 : ‖besselJ (2 * k + 1 : ℕ) (z * Real.cos θ)‖ ≤
            R * (R ^ 2) ^ k * Real.exp (‖z‖ ^ 2 / 4) * (1 / k !) := by
          refine hk1.trans ?_
          rw [hRk, div_eq_mul_one_div]
          gcongr
        have e0 : ‖besselJ (2 * k : ℕ) (z * Real.cos θ)‖ ≤
            (R ^ 2) ^ k * Real.exp (‖z‖ ^ 2 / 4) * (1 / k !) := by
          refine hk0.trans ?_
          rw [hRk', div_eq_mul_one_div]
          gcongr
        have hεk := hε1 k
        calc ‖p‖ * ‖besselJ (2 * k + 1 : ℕ) (z * Real.cos θ)‖ +
              ‖q‖ * ‖ε k‖ * ‖besselJ (2 * k : ℕ) (z * Real.cos θ)‖
            ≤ ‖p‖ * (R * (R ^ 2) ^ k * Real.exp (‖z‖ ^ 2 / 4) * (1 / k !)) +
              ‖q‖ * 1 * ((R ^ 2) ^ k * Real.exp (‖z‖ ^ 2 / 4) * (1 / k !)) := by
              gcongr
          _ = _ := by ring
      calc _ ≤ (‖p‖ * R + ‖q‖) * ((R ^ 2) ^ k / k !) * Real.exp (‖z‖ ^ 2 / 4) *
            Real.exp (‖ν‖ * (π / 2)) :=
            mul_le_mul H (hcos θ hθ) (norm_nonneg _) (by positivity)
        _ = _ := by simp only [E]; ring)
    (Eventually.of_forall fun _ _ => by
      simp only [hB]
      exact ((Real.summable_pow_div_factorial (R ^ 2)).mul_left _).mul_right _)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ => by
      have h := (((hasSum_neg_one_pow_besselJ_odd (z * Real.cos θ)).mul_left p).add
        ((hasSum_neg_one_pow_besselJ_even (z * Real.cos θ)).mul_left q)).mul_right (cos (ν * θ))
      convert h using 1
      · funext k; simp only [hF, hε]; ring
      · ring)
  exact hint

end DLMF.Bessel
