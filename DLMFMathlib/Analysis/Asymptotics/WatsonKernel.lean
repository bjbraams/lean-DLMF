/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.Watson
public import Mathlib.Analysis.MellinTransform

/-!
# Watson estimates for rapidly decreasing kernels

The substitution `u = t^κ` transports the Laplace remainder estimate to stretched
exponentials. Domination then gives Watson's lemma for kernels bounded by such an
exponential. The moment coefficients are Mellin transforms.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Topology

/-- Every real power grows more slowly than a stretched exponential with positive
coefficient and positive stretching exponent. -/
theorem isLittleO_rpow_exp_mul_rpow_atTop {κ b : ℝ} (hκ : 0 < κ) (hb : 0 < b) (r : ℝ) :
    (fun t : ℝ => t ^ r) =o[atTop] (fun t => Real.exp (b * t ^ κ)) := by
  have h := (isLittleO_rpow_exp_pos_mul_atTop (r / κ) hb).comp_tendsto (tendsto_rpow_atTop hκ)
  refine h.congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul ht.le, mul_div_cancel₀ _ hκ.ne']

/-- Stretched exponential decay is smaller than every real power at infinity. -/
theorem isLittleO_exp_neg_mul_rpow_rpow_atTop {κ b : ℝ} (hκ : 0 < κ) (hb : 0 < b) (r : ℝ) :
    (fun t : ℝ => Real.exp (-b * t ^ κ)) =o[atTop] (fun t => t ^ r) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hb (r / κ)).comp_tendsto
    (tendsto_rpow_atTop hκ)
  refine h.congr' .rfl ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul ht.le, mul_div_cancel₀ _ hκ.ne']

/-- A locally integrable function with an integrable power bound at zero and
stretched-exponential growth at infinity becomes integrable after stronger decay. -/
theorem integrableOn_exp_neg_mul_rpow_mul_of_isBigO {G : ℝ → ℝ} {κ b c s : ℝ}
    (hκ : 0 < κ) (hbc : b < c) (hs : 0 < s)
    (hGi : LocallyIntegrableOn G (Ioi 0))
    (hG0 : G =O[𝓝[>] 0] (fun t : ℝ => t ^ (s - 1)))
    (hGtop : G =O[atTop] (fun t => Real.exp (b * t ^ κ))) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * t ^ κ) * G t) (Ioi 0) := by
  have hc : ContinuousOn (fun t : ℝ => Real.exp (-c * t ^ κ)) (Ioi 0) := by
    intro t ht
    fun_prop (disch := exact ht.ne')
  have hloc := hGi.continuousOn_mul hc isOpen_Ioi.isLocallyClosed
  have htop : (fun t : ℝ => Real.exp (-c * t ^ κ) * G t) =O[atTop]
      (fun t : ℝ => t ^ (-2 : ℝ)) := by
    have h := (isBigO_refl (fun t : ℝ => Real.exp (-c * t ^ κ)) atTop).mul hGtop
    have he : (fun t : ℝ => Real.exp (-c * t ^ κ) * Real.exp (b * t ^ κ)) =
        fun t => Real.exp (-(c - b) * t ^ κ) := by
      ext t
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at h
    exact h.trans (isLittleO_exp_neg_mul_rpow_rpow_atTop hκ (by linarith) (-2)).isBigO
  have hzero : (fun t : ℝ => Real.exp (-c * t ^ κ) * G t) =O[𝓝[>] 0]
      (fun t : ℝ => t ^ (s - 1)) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-c * t ^ κ)) (𝓝[>] 0) (𝓝 1) := by
      have hpow : Tendsto (fun t : ℝ => t ^ κ) (𝓝[>] 0) (𝓝 0) :=
        by simpa only [Real.zero_rpow hκ.ne'] using
          (Real.continuousAt_rpow_const 0 κ (Or.inr hκ.le)).tendsto.mono_left nhdsWithin_le_nhds
      simpa only [Function.comp_def, mul_zero, Real.exp_zero] using
        Real.continuous_exp.continuousAt.tendsto.comp (hpow.const_mul (-c))
    simpa only [one_mul] using (isBigO_const_of_tendsto he (by norm_num : (1 : ℝ) ≠ 0)).mul hG0
  simpa only [sub_self, Real.rpow_zero, one_mul] using
    mellin_convergent_of_isBigO_scalar (s := 1) (a := 2) (b := 1 - s) hloc htop
      (by norm_num) (by simpa using hzero) (by linarith)

/-- A positive power substitution expresses a stretched Laplace integral as an
ordinary Laplace integral, including the Jacobian. -/
theorem integral_exp_neg_mul_rpow_mul_eq {G : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ) (z : ℝ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-z * t ^ κ) * G t) =
      ∫ u in Ioi (0 : ℝ), Real.exp (-z * u) *
        (κ⁻¹ * u ^ (κ⁻¹ - 1) * G (u ^ κ⁻¹)) := by
  rw [← integral_comp_rpow_Ioi_of_pos (inv_pos.mpr hκ)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [← Real.rpow_mul hu.le, inv_mul_cancel₀ hκ.ne', Real.rpow_one, smul_eq_mul]
  ring

/-- The power substitution for a stretched Laplace integral preserves absolute
integrability, with its Jacobian included. -/
theorem integrableOn_exp_neg_mul_rpow_mul_iff {G : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ) (z : ℝ) :
    IntegrableOn (fun t => Real.exp (-z * t ^ κ) * G t) (Ioi 0) ↔
      IntegrableOn (fun u : ℝ => Real.exp (-z * u) *
        (κ⁻¹ * u ^ (κ⁻¹ - 1) * G (u ^ κ⁻¹))) (Ioi 0) := by
  rw [← integrableOn_Ioi_comp_rpow_iff
    (fun t => Real.exp (-z * t ^ κ) * G t) (inv_ne_zero hκ.ne')]
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro u hu
  dsimp only
  rw [abs_of_pos (inv_pos.mpr hκ), ← Real.rpow_mul hu.le, inv_mul_cancel₀ hκ.ne',
    Real.rpow_one, smul_eq_mul]
  ring

/-- Increasing the coefficient of stretched exponential decay preserves absolute
integrability on the positive half-line. -/
theorem MeasureTheory.IntegrableOn.exp_neg_mul_rpow_mul_of_le {G : ℝ → ℝ} {κ c z : ℝ}
    (hint : IntegrableOn (fun t => Real.exp (-c * t ^ κ) * G t) (Ioi 0))
    (hκ : 0 < κ) (hcz : c ≤ z) :
    IntegrableOn (fun t => Real.exp (-z * t ^ κ) * G t) (Ioi 0) := by
  rw [integrableOn_exp_neg_mul_rpow_mul_iff hκ] at hint ⊢
  have hi : IntegrableOn (fun u : ℝ => Real.exp (-c * u) •
      (κ⁻¹ * u ^ (κ⁻¹ - 1) * G (u ^ κ⁻¹))) (Ioi 0) := by
    simpa only [smul_eq_mul] using hint
  simpa only [smul_eq_mul] using hi.exp_neg_mul_smul_of_le hcz

/-- A power-law bound at zero is transformed with the Jacobian under a positive
power substitution. -/
theorem isBigO_rpow_jacobian_comp {G : ℝ → ℝ} {κ s : ℝ} (hκ : 0 < κ)
    (hG : G =O[𝓝[>] 0] (fun t : ℝ => t ^ (s - 1))) :
    (fun u : ℝ => κ⁻¹ * u ^ (κ⁻¹ - 1) * G (u ^ κ⁻¹)) =O[𝓝[>] 0]
      (fun u : ℝ => u ^ (s / κ - 1)) := by
  have hp0 : Tendsto (fun u : ℝ => u ^ κ⁻¹) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow (inv_ne_zero hκ.ne')] using
      (Real.continuousAt_rpow_const 0 κ⁻¹ (Or.inr (inv_pos.mpr hκ).le)).tendsto.mono_left
        nhdsWithin_le_nhds
  have hp : Tendsto (fun u : ℝ => u ^ κ⁻¹) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hp0,
      (eventually_mem_nhdsWithin.mono fun u hu => Real.rpow_pos_of_pos hu _)⟩
  have h := ((isBigO_refl (fun u : ℝ => u ^ (κ⁻¹ - 1)) (𝓝[>] 0)).mul
    (hG.comp_tendsto hp)).const_mul_left κ⁻¹
  refine h.congr' (Eventually.of_forall fun u => by simp only [mul_assoc, Function.comp_apply]) ?_
  filter_upwards [eventually_mem_nhdsWithin] with u hu
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hu.le, ← Real.rpow_add hu]
  congr 1
  field_simp
  ring

/-- The Laplace remainder estimate for stretched exponentials follows by a power
substitution from the ordinary Watson remainder estimate. -/
theorem isBigO_integral_exp_neg_mul_rpow_mul {G : ℝ → ℝ} {κ s c : ℝ}
    (hκ : 0 < κ) (hs : 0 < s)
    (hint : IntegrableOn (fun t => Real.exp (-c * t ^ κ) * G t) (Ioi 0))
    (hG : G =O[𝓝[>] 0] (fun t : ℝ => t ^ (s - 1))) :
    (fun z : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-z * t ^ κ) * G t) =O[atTop]
      (fun z : ℝ => z ^ (-(s / κ))) := by
  have hi' : IntegrableOn (fun u : ℝ => Real.exp (-c * u) •
      (κ⁻¹ * u ^ (κ⁻¹ - 1) * G (u ^ κ⁻¹))) (Ioi 0) := by
    simpa only [smul_eq_mul] using (integrableOn_exp_neg_mul_rpow_mul_iff hκ c).mp hint
  have h := isBigO_integral_exp_smul (div_pos hs hκ) hi'
    (isBigO_rpow_jacobian_comp hκ hG)
  simpa only [smul_eq_mul, ← integral_exp_neg_mul_rpow_mul_eq hκ] using h

/-- A measurable stretched-exponentially bounded kernel has absolutely convergent
Mellin moments of every positive real order. -/
theorem mellinConvergent_of_norm_le_exp_rpow {f : ℝ → ℂ} {A a κ s : ℝ}
    (ha : 0 < a) (hκ : 0 < κ) (hs : 0 < s)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ t, 0 ≤ t → ‖f t‖ ≤ A * Real.exp (-a * t ^ κ)) : MellinConvergent f s := by
  have hbase := (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < s - 1)
    hκ ha).const_mul A
  refine hbase.mono' ?_ ?_
  · exact ((continuousOn_of_forall_continuousAt fun (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) =>
      Complex.continuousAt_ofReal_cpow_const t ((s : ℂ) - 1) (Or.inr ht.ne')).aestronglyMeasurable
        measurableSet_Ioi).smul hfm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    calc t ^ (s - 1) * ‖f t‖ ≤ t ^ (s - 1) * (A * Real.exp (-a * t ^ κ)) :=
        mul_le_mul_of_nonneg_left (hf t ht.le) (Real.rpow_nonneg ht.le _)
      _ = _ := by ring

/-- The pointwise kernel bound transfers to a product after positive dilation. -/
lemma norm_kernel_mul_le_exp_rpow {f G : ℝ → ℂ} {A a κ x t : ℝ}
    (hf : ∀ u, 0 ≤ u → ‖f u‖ ≤ A * Real.exp (-a * u ^ κ))
    (hx : 0 ≤ x) (ht : 0 ≤ t) :
    ‖f (x * t) * G t‖ ≤ A * (Real.exp (-(a * x ^ κ) * t ^ κ) * ‖G t‖) := by
  rw [norm_mul]
  have h := mul_le_mul_of_nonneg_right (hf (x * t) (mul_nonneg hx ht)) (norm_nonneg (G t))
  rw [Real.mul_rpow hx ht] at h
  rw [show -a * (x ^ κ * t ^ κ) = -(a * x ^ κ) * t ^ κ by ring] at h
  simpa only [mul_assoc] using h

/-- A dilated rapidly decreasing kernel times a function with an integrable
stretched-exponential weight is integrable once its dilation provides enough decay. -/
theorem integrableOn_kernel_mul_of_exp_rpow {f G : ℝ → ℂ} {A a κ c x : ℝ}
    (ha : 0 < a) (hκ : 0 < κ) (hx : 0 < x) (hcx : c ≤ a * x ^ κ)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Ioi 0)))
    (hf : ∀ t, 0 ≤ t → ‖f t‖ ≤ A * Real.exp (-a * t ^ κ))
    (hint : IntegrableOn (fun t => Real.exp (-c * t ^ κ) * ‖G t‖) (Ioi 0)) :
    IntegrableOn (fun t => f (x * t) * G t) (Ioi 0) := by
  have hfi := mellinConvergent_of_norm_le_exp_rpow ha hκ zero_lt_one hfm hf
  have hfs := (MellinConvergent.comp_mul_left hx).mpr hfi
  have hmeas : AEStronglyMeasurable (fun t => f (x * t)) (volume.restrict (Ioi 0)) := by
    simpa only [MellinConvergent, Complex.ofReal_one, sub_self, Complex.cpow_zero, one_smul] using
      hfs.aestronglyMeasurable
  refine ((hint.exp_neg_mul_rpow_mul_of_le hκ hcx).const_mul A).mono'
    (hmeas.mul hGm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_kernel_mul_le_exp_rpow hf hx.le ht.le

/-- The stretched Laplace remainder bound keeps the order `x⁻ˢ` when the decay
parameter is `a x^κ`. -/
theorem isBigO_integral_exp_neg_mul_rpow_mul_comp {G : ℝ → ℝ} {a κ s c : ℝ}
    (ha : 0 < a) (hκ : 0 < κ) (hs : 0 < s)
    (hint : IntegrableOn (fun t => Real.exp (-c * t ^ κ) * G t) (Ioi 0))
    (hG : G =O[𝓝[>] 0] (fun t : ℝ => t ^ (s - 1))) :
    (fun x : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-(a * x ^ κ) * t ^ κ) * G t) =O[atTop]
      (fun x : ℝ => x ^ (-s)) := by
  have h := (isBigO_integral_exp_neg_mul_rpow_mul hκ hs hint hG).comp_tendsto
    ((tendsto_rpow_atTop hκ).const_mul_atTop ha)
  have he : (fun x : ℝ => (a * x ^ κ) ^ (-(s / κ))) =ᶠ[atTop]
      fun x => a ^ (-(s / κ)) * x ^ (-s) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.mul_rpow ha.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
    congr 1
    field_simp
  exact h.trans ((isBigO_const_mul_self (a ^ (-(s / κ)))
    (fun x : ℝ => x ^ (-s)) atTop).congr' he.symm .rfl)

/-- A kernel with stretched-exponential decay sends a power-law remainder at zero
to a power-law remainder at infinity. -/
theorem isBigO_integral_kernel_mul {f G : ℝ → ℂ} {A a κ b s : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (hκ : 0 < κ) (hs : 0 < s)
    (hf : ∀ t, 0 ≤ t → ‖f t‖ ≤ A * Real.exp (-a * t ^ κ))
    (hGi : LocallyIntegrableOn G (Ioi 0))
    (hG0 : G =O[𝓝[>] 0] (fun t : ℝ => t ^ (s - 1)))
    (hGtop : G =O[atTop] (fun t => Real.exp (b * t ^ κ))) :
    (fun x : ℝ => ∫ t in Ioi (0 : ℝ), f (x * t) * G t) =O[atTop]
      (fun x : ℝ => x ^ (-s)) := by
  have hint := integrableOn_exp_neg_mul_rpow_mul_of_isBigO (c := b + 1)
    hκ (by linarith) hs hGi.norm hG0.norm_left hGtop.norm_left
  have hb := isBigO_integral_exp_neg_mul_rpow_mul_comp ha hκ hs hint hG0.norm_left
  obtain ⟨C, hC⟩ := hb.isBigOWith
  refine IsBigO.of_bound (A * C) ?_
  have hz : ∀ᶠ x : ℝ in atTop, b + 1 ≤ a * x ^ κ :=
    ((tendsto_rpow_atTop hκ).const_mul_atTop ha).eventually (eventually_ge_atTop (b + 1))
  filter_upwards [hC.bound, hz, eventually_gt_atTop 0] with x hx hxz hx0
  have hi := hint.exp_neg_mul_rpow_mul_of_le hκ hxz
  have hnorm : ‖∫ t in Ioi (0 : ℝ), f (x * t) * G t‖ ≤
      A * ∫ t in Ioi (0 : ℝ), Real.exp (-(a * x ^ κ) * t ^ κ) * ‖G t‖ := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hi.const_mul A) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_kernel_mul_le_exp_rpow hf hx0.le ht.le
  calc ‖∫ t in Ioi (0 : ℝ), f (x * t) * G t‖ ≤
      A * ∫ t in Ioi (0 : ℝ), Real.exp (-(a * x ^ κ) * t ^ κ) * ‖G t‖ := hnorm
    _ ≤ A * ‖∫ t in Ioi (0 : ℝ), Real.exp (-(a * x ^ κ) * t ^ κ) * ‖G t‖‖ :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hA
    _ ≤ A * (C * ‖x ^ (-s)‖) := mul_le_mul_of_nonneg_left hx hA
    _ = _ := by ring

/-- A power-weighted kernel integral after positive dilation is its Mellin
moment multiplied by the corresponding inverse power of the dilation. -/
theorem integral_kernel_mul_rpow (f : ℝ → ℂ) (s : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), f (x * t) * ((t ^ (s - 1) : ℝ) : ℂ)) =
      ((x ^ (-s) : ℝ) : ℂ) * mellin f s := by
  have he : (∫ t in Ioi (0 : ℝ), f (x * t) * ((t ^ (s - 1) : ℝ) : ℂ)) =
      mellin (fun t => f (x * t)) s := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow ht.le, smul_eq_mul, mul_comm]
  rw [he, mellin_comp_mul_left f _ hx, smul_eq_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_cpow hx.le]

/-- All positive power moments of a rapidly decreasing measurable kernel are
integrable after positive dilation. -/
theorem integrableOn_kernel_mul_rpow {f : ℝ → ℂ} {A a κ s x : ℝ}
    (ha : 0 < a) (hκ : 0 < κ) (hs : 0 < s) (hx : 0 < x)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ t, 0 ≤ t → ‖f t‖ ≤ A * Real.exp (-a * t ^ κ)) :
    IntegrableOn (fun t : ℝ => f (x * t) * ((t ^ (s - 1) : ℝ) : ℂ)) (Ioi 0) := by
  have hi := (MellinConvergent.comp_mul_left hx).mpr
    (mellinConvergent_of_norm_le_exp_rpow ha hκ hs hfm hf)
  refine IntegrableOn.congr_fun hi (fun t ht => ?_) measurableSet_Ioi
  dsimp only
  rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow ht.le, smul_eq_mul, mul_comm]

/-- A finite power expansion is continuous on the positive half-line, including
negative and nonintegral exponents. -/
lemma continuousOn_rpow_expansion (e : ℕ → ℝ) (a : ℕ → ℂ) (N : ℕ) :
    ContinuousOn (fun t : ℝ => ∑ n ∈ Finset.range N, ((t ^ (e n - 1) : ℝ) : ℂ) * a n) (Ioi 0) := by
  apply continuousOn_finsetSum
  intro n _ t ht
  exact ((Complex.continuous_ofReal.continuousAt.comp
    (Real.continuousAt_rpow_const t (e n - 1) (Or.inl ht.ne'))).mul
      continuousAt_const).continuousWithinAt

/-- Every finite power expansion is dominated at infinity by a growing stretched
exponential. -/
lemma isBigO_rpow_expansion_exp_mul_rpow (e : ℕ → ℝ) (a : ℕ → ℂ) (N : ℕ)
    {κ b : ℝ} (hκ : 0 < κ) (hb : 0 < b) :
    (fun t : ℝ => ∑ n ∈ Finset.range N, ((t ^ (e n - 1) : ℝ) : ℂ) * a n) =O[atTop]
      (fun t : ℝ => Real.exp (b * t ^ κ)) := by
  apply IsBigO.fun_sum
  intro n _
  have h : (fun t : ℝ => ((t ^ (e n - 1) : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (b * t ^ κ)) :=
    Complex.isBigO_ofReal_left.mpr (isLittleO_rpow_exp_mul_rpow_atTop hκ hb _).isBigO
  simpa only [mul_comm] using h.const_mul_left (a n)

/-- A rapidly decreasing kernel can be integrated against a finite power
expansion, giving its Mellin moments term by term. -/
theorem integral_kernel_mul_rpow_expansion {f : ℝ → ℂ} {A a κ : ℝ}
    (ha : 0 < a) (hκ : 0 < κ)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ t, 0 ≤ t → ‖f t‖ ≤ A * Real.exp (-a * t ^ κ))
    (e : ℕ → ℝ) (d : ℕ → ℂ) (he : ∀ n, 0 < e n) (N : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => f (x * t) *
      ∑ n ∈ Finset.range N, ((t ^ (e n - 1) : ℝ) : ℂ) * d n) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), f (x * t) *
        ∑ n ∈ Finset.range N, ((t ^ (e n - 1) : ℝ) : ℂ) * d n) =
        ∑ n ∈ Finset.range N, x ^ (-e n) • (mellin f (e n) * d n) := by
  have hi (n : ℕ) : IntegrableOn (fun t : ℝ =>
      f (x * t) * (((t ^ (e n - 1) : ℝ) : ℂ) * d n)) (Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((integrableOn_kernel_mul_rpow ha hκ (he n) hx hfm hf).mul_const (d n))
      (fun t _ => ?_) measurableSet_Ioi
    ring
  simp_rw [Finset.mul_sum]
  refine ⟨integrable_finsetSum _ fun n _ => hi n, ?_⟩
  rw [integral_finsetSum _ fun n _ => hi n]
  apply Finset.sum_congr rfl
  intro n _
  simp_rw [← mul_assoc]
  rw [integral_mul_const, integral_kernel_mul_rpow f (e n) hx, Complex.real_smul]
  ring

/-- Watson's lemma for a measurable kernel dominated by a stretched exponential,
with any positive sequence of power exponents and Mellin-moment coefficients. -/
theorem hasAsymptoticExpansion_integral_kernel_mul_rpow_seq {f q : ℝ → ℂ} {d : ℕ → ℂ}
    {e : ℕ → ℝ} {A a b κ : ℝ} (he : ∀ n, 0 < e n)
    (hA : 0 ≤ A) (ha : 0 < a) (hb : 0 < b) (hκ : 0 < κ)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ t, 0 ≤ t → ‖f t‖ ≤ A * Real.exp (-a * t ^ κ))
    (hqi : LocallyIntegrableOn q (Ioi 0))
    (hqb : q =O[atTop] (fun t => Real.exp (b * t ^ κ)))
    (hq : ∀ N : ℕ, (fun t => q t - ∑ n ∈ Finset.range N, ((t ^ (e n - 1) : ℝ) : ℂ) * d n)
      =O[𝓝[>] 0] (fun t => t ^ (e N - 1))) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => x ^ (-e n))
      (fun n => mellin f (e n) * d n) (fun x => ∫ t in Ioi (0 : ℝ), f (x * t) * q t) := by
  intro N
  let R : ℝ → ℂ := fun t => q t - ∑ n ∈ Finset.range N, ((t ^ (e n - 1) : ℝ) : ℂ) * d n
  have hRi : LocallyIntegrableOn R (Ioi 0) := hqi.sub
    ((continuousOn_rpow_expansion e d N).locallyIntegrableOn measurableSet_Ioi)
  have hRb : R =O[atTop] (fun t => Real.exp (b * t ^ κ)) :=
    hqb.sub (isBigO_rpow_expansion_exp_mul_rpow e d N hκ hb)
  have hR0 : R =O[𝓝[>] 0] (fun t => t ^ (e N - 1)) := hq N
  have hzero : q =O[𝓝[>] 0] (fun t => t ^ (e 0 - 1)) := by simpa using hq 0
  have hiq := integrableOn_exp_neg_mul_rpow_mul_of_isBigO (c := b + 1)
    hκ (by linarith) (he 0) hqi.norm hzero.norm_left hqb.norm_left
  refine (isBigO_integral_kernel_mul hA ha hκ (he N) hf hRi hR0 hRb).congr' ?_ .rfl
  have hz : ∀ᶠ x : ℝ in atTop, b + 1 ≤ a * x ^ κ :=
    ((tendsto_rpow_atTop hκ).const_mul_atTop ha).eventually (eventually_ge_atTop (b + 1))
  filter_upwards [hz, eventually_gt_atTop 0] with x hxz hx
  have hi := integrableOn_kernel_mul_of_exp_rpow ha hκ hx hxz hfm
    hqi.aestronglyMeasurable hf hiq
  obtain ⟨hiP, heP⟩ := integral_kernel_mul_rpow_expansion ha hκ hfm hf e d he N hx
  dsimp only [R]
  simp_rw [mul_sub]
  rw [integral_sub hi hiP, heP]
