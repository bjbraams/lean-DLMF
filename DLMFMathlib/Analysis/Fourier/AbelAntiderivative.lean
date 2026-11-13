/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Abel sine integrals of bounded antiderivatives

For a bounded antiderivative `f` with `f 0 = 0` and integrable derivative, the exponentially
regularized sine integral tends to `1 / x` times the cosine integral of its derivative.

Integration by parts against the decaying trigonometric primitive gives an explicit formula
for positive damping. Dominated convergence then removes the damping from the derivative.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace Real

set_option maxHeartbeats 0

/-- The Abel sine integral of a bounded antiderivative is the cosine integral of its
derivative divided by the nonzero frequency. Differentiability is required only on the open
positive half-line, and continuity at zero supplies the boundary condition. -/
lemma tendsto_integral_Ioi_exp_mul_sin_of_bounded_antiderivative
    {f f' : ℝ → ℝ} (hf0 : f 0 = 0) (hfc : ContinuousOn f (Ici 0))
    (hfd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hfb : ∃ M : ℝ, ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M)
    (hfi : IntegrableOn f' (Ioi 0)) {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), exp (-ε * t) * f t * sin (x * t))
      (𝓝[>] 0) (𝓝 ((1 / x) * ∫ t in Ioi (0 : ℝ), f' t * cos (x * t))) := by
  have ht0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  obtain ⟨M, hM⟩ := hfb
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (by simp))
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)) :=
    (hfc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have hsin : IntegrableOn (fun t => f' t * sin (x * t)) (Ioi 0) :=
    hfi.mul_bdd (by fun_prop) (Filter.Eventually.of_forall fun t => by
      simpa only [norm_eq_abs] using abs_sin_le_one (x * t))
  have hcos : IntegrableOn (fun t => f' t * cos (x * t)) (Ioi 0) :=
    hfi.mul_bdd (by fun_prop) (Filter.Eventually.of_forall fun t => by
      simpa only [norm_eq_abs] using abs_cos_le_one (x * t))
  have hdamp {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) :
      Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), exp (-ε * t) * g t)
        (𝓝[>] 0) (𝓝 (∫ t in Ioi (0 : ℝ), g t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖g t‖) ?_ ?_
      hg.norm ?_
    · exact Eventually.of_forall fun ε => (by fun_prop : Continuous fun t => exp (-ε * t))
        |>.aestronglyMeasurable.mul hg.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_eq_abs, abs_of_pos (exp_pos _)]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (exp_le_one_iff.mpr (by nlinarith [hε.out, ht.out]))
    · exact Eventually.of_forall fun t => by
        simpa using ((Real.continuous_exp.continuousAt.tendsto.comp
          (ht0.neg.mul_const t)).mul_const (g t))
  have hA := hdamp hsin
  have hB := hdamp hcos
  have hform (ε : ℝ) (hε : 0 < ε) :
      (∫ t in Ioi (0 : ℝ), exp (-ε * t) * f t * sin (x * t)) =
        (ε * (∫ t in Ioi (0 : ℝ), exp (-ε * t) * (f' t * sin (x * t))) +
          x * (∫ t in Ioi (0 : ℝ), exp (-ε * t) * (f' t * cos (x * t)))) /
            (ε ^ 2 + x ^ 2) := by
    let v : ℝ → ℝ := fun t => exp (-ε * t) * (ε * sin (x * t) + x * cos (x * t))
    let v' : ℝ → ℝ := fun t => -(ε ^ 2 + x ^ 2) * exp (-ε * t) * sin (x * t)
    have hv (t : ℝ) (_ht : t ∈ Ioi (0 : ℝ)) : HasDerivAt v (v' t) t := by
      have he := (((hasDerivAt_id t).const_mul (-ε)).exp)
      have hs := (((hasDerivAt_id t).const_mul x).sin).const_mul ε
      have hc := (((hasDerivAt_id t).const_mul x).cos).const_mul x
      have hd := he.mul (hs.add hc)
      simp only [Pi.mul_def, Pi.add_def, id_eq, mul_one] at hd
      convert hd using 1
      dsimp only [v, v']
      ring_nf
    have hiE := integrableOn_exp_mul_Ioi (neg_neg_of_pos hε) 0
    have hiF : IntegrableOn (fun t => exp (-ε * t) * f t) (Ioi 0) :=
      hiE.mul_bdd hfm (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hM t ht.le)
    have hiFs : IntegrableOn (fun t => exp (-ε * t) * f t * sin (x * t)) (Ioi 0) :=
      hiF.mul_bdd (by fun_prop) (Eventually.of_forall fun t => by
        simpa only [norm_eq_abs] using abs_sin_le_one (x * t))
    have hiA : IntegrableOn (fun t => exp (-ε * t) * (f' t * sin (x * t))) (Ioi 0) :=
      hsin.bdd_mul (by fun_prop) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        simpa only [norm_eq_abs, abs_of_pos (exp_pos _)] using
          exp_le_one_iff.mpr (show -ε * t ≤ 0 by nlinarith [hε, ht.out]))
    have hiB : IntegrableOn (fun t => exp (-ε * t) * (f' t * cos (x * t))) (Ioi 0) :=
      hcos.bdd_mul (by fun_prop) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        simpa only [norm_eq_abs, abs_of_pos (exp_pos _)] using
          exp_le_one_iff.mpr (show -ε * t ≤ 0 by nlinarith [hε, ht.out]))
    have huv' : IntegrableOn (f * v') (Ioi 0) := by
      refine IntegrableOn.congr_fun (s := Ioi 0)
        (hiFs.const_mul (-(ε ^ 2 + x ^ 2))) (fun t _ => ?_) measurableSet_Ioi
      dsimp only [Pi.mul_apply, v']
      ring_nf
    have hu'v : IntegrableOn (f' * v) (Ioi 0) := by
      refine IntegrableOn.congr_fun (s := Ioi 0) ((hiA.const_mul ε).add (hiB.const_mul x))
        (fun t _ => ?_) measurableSet_Ioi
      dsimp only [Pi.mul_apply, Pi.add_apply, v]
      ring_nf
    have hzero : Tendsto (f * v) (𝓝[>] 0) (𝓝 0) := by
      have hvcont : Continuous v := by dsimp only [v]; fun_prop
      have h := ((hfc 0 (by simp)).mono Ioi_subset_Ici_self).tendsto.mul
        (hvcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      simpa only [Pi.mul_def, hf0, zero_mul] using h
    have hinf : Tendsto (f * v) atTop (𝓝 0) := by
      have he : Tendsto (fun t : ℝ => exp (-ε * t)) atTop (𝓝 0) :=
        tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hε))
      have hh := he.mul_const (M * (|ε| + |x|))
      simp only [zero_mul] at hh
      refine squeeze_zero_norm' ?_ hh
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      dsimp only [Pi.mul_apply, v]
      rw [norm_mul, norm_mul]
      simp only [norm_eq_abs, abs_of_pos (exp_pos _)]
      calc
        _ ≤ M * (exp (-ε * t) * (|ε| + |x|)) := by
          gcongr
          · exact hM t ht
          · calc
              |ε * sin (x * t) + x * cos (x * t)| ≤
                  |ε| * |sin (x * t)| + |x| * |cos (x * t)| := by
                    simpa only [abs_mul] using abs_add_le (ε * sin (x * t)) (x * cos (x * t))
              _ ≤ _ := add_le_add
                (mul_le_of_le_one_right (abs_nonneg ε) (abs_sin_le_one (x * t)))
                (mul_le_of_le_one_right (abs_nonneg x) (abs_cos_le_one (x * t)))
        _ = _ := by ring_nf
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hfd hv huv' hu'v hzero hinf
    have hl : (∫ t in Ioi (0 : ℝ), f t * v' t) =
        -(ε ^ 2 + x ^ 2) * (∫ t in Ioi (0 : ℝ), exp (-ε * t) * f t * sin (x * t)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by dsimp only [v']; ring_nf
    have hr : (∫ t in Ioi (0 : ℝ), f' t * v t) =
        ε * (∫ t in Ioi (0 : ℝ), exp (-ε * t) * (f' t * sin (x * t))) +
          x * (∫ t in Ioi (0 : ℝ), exp (-ε * t) * (f' t * cos (x * t))) := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add
        (hiA.const_mul ε) (hiB.const_mul x)]
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by dsimp only [v]; ring_nf
    rw [hl, hr] at hibp
    apply (eq_div_iff (by positivity : ε ^ 2 + x ^ 2 ≠ 0)).mpr
    linear_combination -hibp
  have hlim := (ht0.mul hA |>.add
    (hB.const_mul x)).div
      ((ht0.pow 2).add_const (x ^ 2))
      (by simpa only [zero_pow two_ne_zero, zero_add] using pow_ne_zero 2 hx)
  simp only [zero_mul, zero_add, zero_pow two_ne_zero] at hlim
  have hval : (x * (∫ t in Ioi (0 : ℝ), f' t * cos (x * t))) / x ^ 2 =
      (1 / x) * ∫ t in Ioi (0 : ℝ), f' t * cos (x * t) := by field_simp [hx]
  rw [hval] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hform ε hε).symm

end Real
