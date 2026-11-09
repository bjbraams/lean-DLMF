/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonLog

/-!
# Complex logarithmic moments for Watson's lemma

The logarithmic Gamma moment for a complex order `s` with `Re s > 0` is
`∫ exp (-x t) t^(s-1) log t = (Γ'(s) - log x Γ(s)) x^(-s)`, for real `x > 0`.
This is the complex-exponent kernel in the logarithmic Watson lemma, DLMF 2.3.9.
The proof uses Mathlib's differentiation theorem for Mellin transforms and the proved
complex-order Gamma integral in `Watson`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace Complex

/-- The Mellin transform of `exp (-x t) log t`, for positive real `x` and `Re s > 0`. -/
theorem hasMellin_exp_neg_mul_log {s : ℂ} {x : ℝ} (hs : 0 < s.re) (hx : 0 < x) :
    HasMellin (fun t : ℝ => (Real.exp (-x * t) * Real.log t : ℂ)) s
      ((deriv Complex.Gamma s - (Real.log x : ℂ) * Complex.Gamma s) * (x : ℂ) ^ (-s)) := by
  let f : ℝ → ℂ := fun t => (Real.exp (-x * t) : ℂ)
  have hc : Continuous f := by dsimp [f]; fun_prop
  have htop : f =O[atTop] (fun t : ℝ => t ^ (-(s.re + 1))) := by
    simpa only [f, Complex.isBigO_ofReal_left] using
      (isLittleO_exp_neg_mul_rpow_atTop hx (-(s.re + 1))).isBigO
  have hbot : f =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) :=
    isBigO_const_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) one_ne_zero
  have hm := mellin_hasDerivAt_of_isBigO_rpow
    (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi) htop
    (lt_add_one s.re) (by simpa using hbot) hs
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hmodel : mellin f =ᶠ[𝓝 s]
      (fun u : ℂ => Complex.Gamma u * Complex.exp (-u * Complex.log (x : ℂ))) := by
    have hU : {u : ℂ | 0 < u.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const continuous_re).mem_nhds hs
    filter_upwards [hU] with u hu
    calc mellin f u = ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) • (t : ℂ) ^ (u - 1) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t _
          simp only [f, smul_eq_mul, Complex.real_smul]
          ring
      _ = Complex.Gamma u * (x : ℂ) ^ (-u) :=
        integral_exp_neg_mul_smul_cpow_sub_one hu hx
      _ = _ := by
        rw [cpow_def_of_ne_zero hx0]
        congr 2
        ring
  have hd := (((hasDerivAt_Gamma_of_re_pos hs).differentiableAt.hasDerivAt).mul
    (((hasDerivAt_id s).neg.mul_const (Complex.log (x : ℂ))).cexp)).congr_of_eventuallyEq hmodel
  have he := hm.2.unique hd
  constructor
  · convert hm.1 using 1
    funext t
    simp only [f, Complex.real_smul]
    ring
  · convert he using 1
    · congr 1
      funext t
      simp only [f, Complex.real_smul]
      ring
    · rw [cpow_def_of_ne_zero hx0, ← ofReal_log hx.le]
      simp only [Pi.neg_apply, id_eq]
      ring

/-- The complex logarithmic Gamma kernel is absolutely integrable. -/
theorem integrableOn_exp_neg_mul_cpow_sub_one_mul_log {s : ℂ} {x : ℝ}
    (hs : 0 < s.re) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (Real.exp (-x * t) : ℂ) *
      (t : ℂ) ^ (s - 1) * (Real.log t : ℂ)) (Ioi 0) := by
  refine (hasMellin_exp_neg_mul_log hs hx).1.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  ring

/-- The exact logarithmic Gamma moment with complex order and positive real decay. -/
theorem integral_exp_neg_mul_cpow_sub_one_mul_log {s : ℂ} {x : ℝ}
    (hs : 0 < s.re) (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), (Real.exp (-x * t) : ℂ) *
      (t : ℂ) ^ (s - 1) * (Real.log t : ℂ)) =
      (deriv Complex.Gamma s - (Real.log x : ℂ) * Complex.Gamma s) * (x : ℂ) ^ (-s) := by
  rw [← (hasMellin_exp_neg_mul_log hs hx).2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [smul_eq_mul]
  ring

end Complex

namespace Asymptotics

/-- A locally integrable logarithmic factor preserves absolute Laplace convergence after
increasing the real decay parameter, provided the order at zero is integrable. -/
theorem integrableOn_exp_neg_mul_log_smul {F : ℝ → ℂ} {s c : ℝ} (hs : 0 < s)
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • F t) (Ioi 0))
    (hF : F =O[𝓝[>] 0] fun t => t ^ (s - 1)) :
    IntegrableOn (fun t => Real.exp (-(c + 1) * t) • (Real.log t • F t)) (Ioi 0) := by
  let G : ℝ → ℂ := fun t => Real.exp (-c * t) • F t
  let g : ℝ → ℂ := (Iic (1 : ℝ)).indicator G
  have hloc : LocallyIntegrableOn g (Ioi 0) := by
    intro x hx
    obtain ⟨U, hU, hUi⟩ := hint.locallyIntegrableOn x hx
    exact ⟨U, hU, hUi.indicator measurableSet_Iic⟩
  have htop : g =O[atTop] (fun t : ℝ => t ^ (-2 : ℝ)) := by
    refine (isBigO_zero _ _).congr' ?_ .rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [g, not_le.mpr ht]
  have hbot : g =O[𝓝[>] 0] (fun t : ℝ => t ^ (s - 1)) := by
    have helim : Tendsto (fun t : ℝ => Real.exp (-c * t)) (𝓝[>] 0) (𝓝 1) := by
      have hcont : Continuous (fun t : ℝ => Real.exp (-c * t)) := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have he : (fun t : ℝ => Real.exp (-c * t)) =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) :=
      isBigO_const_of_tendsto helim one_ne_zero
    have hG := he.smul hF
    refine hG.congr' ?_ (Eventually.of_forall fun t => by simp)
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    simp only [g, indicator_of_mem (show t ∈ Iic (1 : ℝ) from ht.2.le), G]
  have hm := (mellin_hasDerivAt_of_isBigO_rpow (s := (1 : ℂ)) (b := 1 - s)
    hloc htop (by norm_num) (by simpa only [neg_sub, sub_zero] using hbot)
    (by simp; linarith)).1
  let L : ℝ → ℂ := fun t => Real.log t • g t
  have hLi : IntegrableOn L (Ioi 0) := by
    simpa only [MellinConvergent, sub_self, cpow_zero, one_smul] using hm
  have hLow : IntegrableOn (fun t => Real.exp (-t) • L t) (Ioi 0) := by
    refine hLi.norm.mono'
      (((by fun_prop : Continuous fun t : ℝ => Real.exp (-t)).aestronglyMeasurable).smul
        hLi.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_of_lt (show 0 < t from ht))))
  have hHigh : IntegrableOn (fun t =>
      (Ioi (1 : ℝ)).indicator (fun t => Real.exp (-t) * Real.log t) t • G t) (Ioi 0) := by
    refine hint.norm.mono' ?_ ?_
    · exact ((Real.continuous_exp.comp continuous_neg).measurable.mul Real.measurable_log
        |>.indicator measurableSet_Ioi |>.aestronglyMeasurable).smul hint.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
      rw [norm_smul]
      apply mul_le_of_le_one_left (norm_nonneg _)
      by_cases ht : 1 < t
      · rw [indicator_of_mem ht, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.log_nonneg ht.le))]
        calc Real.exp (-t) * Real.log t ≤ Real.exp (-t) * t :=
            mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith)) (Real.exp_pos _).le
          _ ≤ Real.exp (-t) * Real.exp t :=
            mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp t]) (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add]; simp
      · simp only [indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from ht), norm_zero, zero_le_one]
  refine (hLow.add hHigh).congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, L, g, G]
  have he : Real.exp (-t) * Real.exp (-c * t) = Real.exp (-(c + 1) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  by_cases ht : t ≤ 1
  · simp only [indicator_of_mem (show t ∈ Iic (1 : ℝ) from ht),
      indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt.mpr ht), smul_smul,
      zero_mul, zero_smul, add_zero]
    rw [← he]
    congr 1
    ring
  · simp only [indicator_of_notMem (show t ∉ Iic (1 : ℝ) from ht), smul_zero,
      indicator_of_mem (show t ∈ Ioi (1 : ℝ) from not_le.mp ht),
      zero_add, smul_smul]
    rw [← he]
    congr 1
    ring

/-- A complex logarithmic Gamma moment has order `x^(-Re s) log x` on the positive real axis. -/
theorem isBigO_log_gamma_term_cpow (s a : ℂ) :
    (fun x : ℝ => (deriv Complex.Gamma s - (Real.log x : ℂ) * Complex.Gamma s) * a *
      (x : ℂ) ^ (-s)) =O[atTop] (fun x : ℝ => x ^ (-s.re) * Real.log x) := by
  refine IsBigO.of_bound ((‖deriv Complex.Gamma s‖ + ‖Complex.Gamma s‖) * ‖a‖) ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hlog : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hbound : ‖deriv Complex.Gamma s - (Real.log x : ℂ) * Complex.Gamma s‖ ≤
      (‖deriv Complex.Gamma s‖ + ‖Complex.Gamma s‖) * Real.log x := by
    calc _ ≤ ‖deriv Complex.Gamma s‖ + ‖(Real.log x : ℂ) * Complex.Gamma s‖ := norm_sub_le _ _
      _ = ‖deriv Complex.Gamma s‖ + Real.log x * ‖Complex.Gamma s‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      _ ≤ _ := by nlinarith [norm_nonneg (deriv Complex.Gamma s)]
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, neg_re,
    Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (by linarith))]
  calc _ ≤ ((‖deriv Complex.Gamma s‖ + ‖Complex.Gamma s‖) * Real.log x) *
        ‖a‖ * x ^ (-s.re) := by gcongr
    _ = _ := by ring

/-- The logarithmic Watson lemma for a general sequence of complex exponents with strictly
increasing positive real parts. Absolute Laplace convergence of `F` suffices: the extra
logarithmic factor is integrable at a slightly larger decay parameter. -/
theorem isBigO_laplace_log_sub_sum_cpow {F : ℝ → ℂ} {e a : ℕ → ℂ} {c : ℝ}
    (he : ∀ n, 0 < (e n).re) (hstep : ∀ n, (e n).re < (e (n + 1)).re)
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • F t) (Ioi 0))
    (hF : ∀ N : ℕ, (fun t => F t - ∑ n ∈ Finset.range N, (t : ℂ) ^ (e n - 1) • a n)
      =O[𝓝[>] 0] fun t => t ^ ((e N).re - 1)) (N : ℕ) :
    (fun x : ℝ => (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) • (Real.log t • F t)) -
      ∑ n ∈ Finset.range N,
        (deriv Complex.Gamma (e n) - (Real.log x : ℂ) * Complex.Gamma (e n)) * a n *
          (x : ℂ) ^ (-e n)) =O[atTop] fun x => x ^ (-(e N).re) * Real.log x := by
  have hintlog := integrableOn_exp_neg_mul_log_smul (he 0) hint
    (by simpa only [Finset.range_zero, Finset.sum_empty, sub_zero] using hF 0)
  let c' := max (c + 1) 0 + 1
  have hc' : 0 < c' := by dsimp [c']; linarith [le_max_right (c + 1) 0]
  have hcc' : c + 1 ≤ c' := by dsimp [c']; linarith [le_max_left (c + 1) 0]
  have hi (x : ℝ) (hx : c + 1 ≤ x) :
      IntegrableOn (fun t => Real.exp (-x * t) • (Real.log t • F t)) (Ioi 0) :=
    hintlog.exp_neg_mul_smul_of_le hx
  have ht (n : ℕ) (x : ℝ) (hx : 0 < x) : IntegrableOn (fun t : ℝ =>
      Real.exp (-x * t) • (Real.log t • ((t : ℂ) ^ (e n - 1) • a n))) (Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((Complex.integrableOn_exp_neg_mul_cpow_sub_one_mul_log (he n) hx).mul_const (a n))
      (fun t _ => ?_) measurableSet_Ioi
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  have htval (n : ℕ) (x : ℝ) (hx : 0 < x) :
      (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) •
        (Real.log t • ((t : ℂ) ^ (e n - 1) • a n))) =
      (deriv Complex.Gamma (e n) - (Real.log x : ℂ) * Complex.Gamma (e n)) * a n *
        (x : ℂ) ^ (-e n) := by
    have h := congrArg (fun z : ℂ => z * a n)
      (Complex.integral_exp_neg_mul_cpow_sub_one_mul_log (he n) hx)
    rw [← integral_mul_const] at h
    convert h using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [Complex.real_smul, smul_eq_mul]
      ring
    · ring
  let R : ℝ → ℂ := fun t => F t -
    ∑ n ∈ Finset.range (N + 1), (t : ℂ) ^ (e n - 1) • a n
  have hintR : IntegrableOn (fun t => Real.exp (-c' * t) • (Real.log t • R t)) (Ioi 0) := by
    have h := (hi c' hcc').sub (integrable_finsetSum (Finset.range (N + 1))
      (fun n _ => ht n c' hc'))
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [R, Pi.sub_apply, smul_sub, Finset.smul_sum]
  have hsmall := isBigO_rpow_zero_log_smul
    (a := -((e (N + 1)).re - 1)) (b := -((e N).re - 1))
    (by linarith [hstep N]) (by simpa only [neg_neg] using hF (N + 1))
  have hb := isBigO_integral_exp_smul (he N) hintR
    (by simpa only [neg_neg] using hsmall)
  have hscale : (fun x : ℝ => x ^ (-(e N).re)) =O[atTop]
      (fun x : ℝ => x ^ (-(e N).re) * Real.log x) := by
    simpa only [mul_one] using (isBigO_refl (fun x : ℝ => x ^ (-(e N).re)) atTop).mul
      (Real.isLittleO_const_log_atTop (c := 1)).isBigO
  refine ((hb.trans hscale).add (isBigO_log_gamma_term_cpow (e N) (a N))).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop c'] with x hx
  have hx0 : 0 < x := hc'.trans_le hx
  simp only [R, smul_sub, Finset.smul_sum]
  rw [integral_sub (hi x (hcc'.trans hx))
      (integrable_finsetSum (Finset.range (N + 1)) (fun n _ => ht n x hx0)),
    integral_finsetSum _ (fun n _ => ht n x hx0)]
  simp_rw [htval _ _ hx0]
  rw [Finset.sum_range_succ]
  ring

end Asymptotics
