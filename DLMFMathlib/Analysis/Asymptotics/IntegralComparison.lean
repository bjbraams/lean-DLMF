/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Integrating power-law asymptotics

A continuous function dominated at infinity by an integrable complex power is
integrable on a positive half-line. Asymptotic equivalence to such a power passes
to the tail integral, by integrating the uniform tail bound on the error.
For nonintegrable powers, asymptotic equivalence instead passes to growing
primitives; the fixed initial segment becomes negligible. The borderline
comparison with `1/x` gives a logarithmic primitive.
-/

@[expose] public noncomputable section

open Filter Set Asymptotics MeasureTheory Complex
open scoped Topology

/-- A continuous function with an integrable power-law bound at infinity is integrable
on the whole closed positive half-line on which it is continuous. -/
theorem ContinuousOn.integrableOn_Ici_of_isBigO_cpow {f : ℝ → ℂ} {ν : ℂ} {a : ℝ}
    (hf : ContinuousOn f (Ici a)) (ha : 0 < a) (hν : ν.re < -1)
    (hO : f =O[atTop] fun x => (x : ℂ) ^ ν) : IntegrableOn f (Ici a) := by
  have hg : IntegrableAtFilter (fun t : ℝ => (t : ℂ) ^ ν) atTop volume :=
    ⟨Ioi a, Ioi_mem_atTop a, integrableOn_Ioi_cpow_of_lt hν ha⟩
  exact (hf.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop hO hg

/-- Integrating an asymptotic complex power with real part below `-1` from `x` to
infinity preserves its leading term, including its complex phase. -/
theorem Asymptotics.IsEquivalent.integral_Ioi_cpow {f : ℝ → ℂ} {ν : ℂ} {a : ℝ}
    (h : f ~[atTop] fun x => (x : ℂ) ^ ν) (ha : 0 < a)
    (hf : ContinuousOn f (Ici a)) (hν : ν.re < -1) :
    (fun x => ∫ t in Ioi x, f t) ~[atTop] fun x => -(x : ℂ) ^ (ν + 1) / (ν + 1) := by
  have hi := hf.integrableOn_Ici_of_isBigO_cpow ha hν h.isBigO
  have hn : ν + 1 ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [add_re, one_re, zero_re] at hr
    linarith
  have hnn : ‖ν + 1‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  refine IsLittleO.of_bound fun ε hε => ?_
  let c := ε * (-(ν.re + 1)) / ‖ν + 1‖
  have hc : 0 < c := div_pos (mul_pos hε (by linarith)) (norm_pos_iff.mpr hn)
  obtain ⟨A, hA⟩ := eventually_atTop.mp (h.isLittleO.bound hc)
  filter_upwards [eventually_ge_atTop A, eventually_gt_atTop a] with x hxA hxa
  have hx : 0 < x := ha.trans hxa
  have hfi : IntegrableOn f (Ioi x) := hi.mono_set fun t ht => le_of_lt (hxa.trans ht)
  have hgi := integrableOn_Ioi_cpow_of_lt hν hx
  have hbound : ‖∫ t in Ioi x, f t - (t : ℂ) ^ ν‖ ≤
      c * (-(x ^ (ν.re + 1)) / (ν.re + 1)) := by
    have hb := norm_integral_le_of_norm_le
      ((integrableOn_Ioi_rpow_of_lt hν hx).const_mul c)
      ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => by
        have he := hA t (hxA.trans ht.le)
        simpa only [Pi.sub_apply, Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans ht)] using he)
    simpa only [integral_const_mul, integral_Ioi_rpow_of_lt hν hx] using hb
  change ‖(∫ t in Ioi x, f t) - (-(x : ℂ) ^ (ν + 1) / (ν + 1))‖ ≤ _
  rw [← integral_Ioi_cpow_of_lt hν hx, ← integral_sub hfi hgi]
  refine hbound.trans_eq ?_
  rw [integral_Ioi_cpow_of_lt hν hx, norm_div, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, add_re, one_re]
  dsimp [c]
  field_simp [hnn, show ν.re + 1 ≠ 0 by linarith, show 1 + ν.re ≠ 0 by linarith]

/-- A little-o bound can be integrated from a fixed endpoint when the nonnegative
comparison integral tends to infinity. The fixed initial segment becomes negligible. -/
theorem Asymptotics.IsLittleO.intervalIntegral_of_nonneg {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {g : ℝ → ℝ} {a : ℝ} (h : f =o[atTop] g)
    (hf : ContinuousOn f (Ici a)) (hg : ContinuousOn g (Ici a))
    (hg0 : ∀ x ∈ Ici a, 0 ≤ g x)
    (hG : Tendsto (fun x => ∫ t in a..x, g t) atTop atTop) :
    (fun x => ∫ t in a..x, f t) =o[atTop] fun x => ∫ t in a..x, g t := by
  have hif {b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : IntervalIntegrable f volume b c :=
    (hf.mono (by rw [uIcc_of_le hbc]; exact fun t ht => hab.trans ht.1)).intervalIntegrable
  have hig {b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : IntervalIntegrable g volume b c :=
    (hg.mono (by rw [uIcc_of_le hbc]; exact fun t ht => hab.trans ht.1)).intervalIntegrable
  refine IsLittleO.of_bound fun ε hε => ?_
  obtain ⟨A, hA⟩ := eventually_atTop.mp (h.bound (half_pos hε))
  let b := max a A
  have hab : a ≤ b := le_max_left _ _
  have hAb : A ≤ b := le_max_right _ _
  let C := ‖∫ t in a..b, f t‖ + ε / 2 * |∫ t in a..b, g t|
  have hC : ∀ᶠ x in atTop, C ≤ ε / 2 * ∫ t in a..x, g t :=
    (hG.const_mul_atTop (half_pos hε)).eventually (eventually_ge_atTop C)
  filter_upwards [eventually_ge_atTop b, hC] with x hbx hxC
  have hax := hab.trans hbx
  have hG0 : 0 ≤ ∫ t in a..x, g t :=
    intervalIntegral.integral_nonneg hax fun t ht => hg0 t ht.1
  have hb := intervalIntegral.norm_integral_le_of_norm_le hbx
    (Eventually.of_forall fun t ht => by
      have he := hA t (hAb.trans ht.1.le)
      rwa [Real.norm_of_nonneg (hg0 t (hab.trans ht.1.le))] at he)
    ((hig hab hbx).const_mul (ε / 2))
  rw [intervalIntegral.integral_const_mul] at hb
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hig le_rfl hab) (hig hab hbx)
  have hfsplit := intervalIntegral.integral_add_adjacent_intervals (hif le_rfl hab) (hif hab hbx)
  rw [← hfsplit, Real.norm_of_nonneg hG0]
  calc ‖(∫ t in a..b, f t) + ∫ t in b..x, f t‖ ≤
      ‖∫ t in a..b, f t‖ + ‖∫ t in b..x, f t‖ := norm_add_le _ _
    _ ≤ ‖∫ t in a..b, f t‖ + ε / 2 * ∫ t in b..x, g t := add_le_add le_rfl hb
    _ ≤ C + ε / 2 * ∫ t in a..x, g t := by
      dsimp [C]
      nlinarith [neg_abs_le (∫ t in a..b, g t)]
    _ ≤ ε * ∫ t in a..x, g t := by linarith

/-- Asymptotic equivalence passes to primitives if the integral of the reference
norm diverges and is bounded by the proposed leading primitive. -/
theorem Asymptotics.IsEquivalent.intervalIntegral_of_integral_norm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g F : ℝ → E} {a : ℝ} (h : f ~[atTop] g)
    (hf : ContinuousOn f (Ici a)) (hg : ContinuousOn g (Ici a))
    (hF : (fun x => ∫ t in a..x, g t) ~[atTop] F)
    (hO : (fun x => ∫ t in a..x, ‖g t‖) =O[atTop] F)
    (hG : Tendsto (fun x => ∫ t in a..x, ‖g t‖) atTop atTop) :
    (fun x => ∫ t in a..x, f t) ~[atTop] F := by
  have he : (f - g) =o[atTop] fun x => ‖g x‖ := isLittleO_norm_right.mpr h.isLittleO
  have hi := he.intervalIntegral_of_nonneg (hf.sub hg) hg.norm (fun x _ => norm_nonneg _) hG
  refine (hF.add_isLittleO (hi.trans_isBigO hO)).congr_left ?_
  filter_upwards [eventually_ge_atTop a] with x hx
  have hfi : IntervalIntegrable f volume a x :=
    (hf.mono (by rw [uIcc_of_le hx]; exact Icc_subset_Ici_self)).intervalIntegrable
  have hgi : IntervalIntegrable g volume a x :=
    (hg.mono (by rw [uIcc_of_le hx]; exact Icc_subset_Ici_self)).intervalIntegrable
  simp only [Pi.add_apply, Pi.sub_apply, intervalIntegral.integral_sub hfi hgi]
  abel

/-- Integrating a continuous function asymptotic to a complex power with real part
above `-1` gives the corresponding growing power-law primitive. -/
theorem Asymptotics.IsEquivalent.intervalIntegral_cpow {f : ℝ → ℂ} {ν : ℂ} {a : ℝ}
    (h : f ~[atTop] fun x => (x : ℂ) ^ ν) (ha : 0 < a)
    (hf : ContinuousOn f (Ici a)) (hν : -1 < ν.re) :
    (fun x => ∫ t in a..x, f t) ~[atTop] fun x => (x : ℂ) ^ (ν + 1) / (ν + 1) := by
  have hp : 0 < ν.re + 1 := by linarith
  have hn : ν + 1 ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [add_re, one_re, zero_re] at hr
    linarith
  have hnn : ‖ν + 1‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have hg : ContinuousOn (fun x : ℝ => (x : ℂ) ^ ν) (Ici a) := by
    intro x hx
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (ha.trans_le hx).ne')).continuousWithinAt
  have hnormInt (x : ℝ) (hx : a ≤ x) :
      (∫ t in a..x, ‖(t : ℂ) ^ ν‖) =
        (x ^ (ν.re + 1) - a ^ (ν.re + 1)) / (ν.re + 1) := by
    have he : (∫ t in a..x, ‖(t : ℂ) ^ ν‖) = ∫ t in a..x, t ^ ν.re := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hx] at ht
      exact Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le ht.1) ν
    rw [he, integral_rpow (Or.inl hν)]
  have hG : Tendsto (fun x => ∫ t in a..x, ‖(t : ℂ) ^ ν‖) atTop atTop := by
    have hsub : Tendsto (fun x : ℝ => x ^ (ν.re + 1) - a ^ (ν.re + 1)) atTop atTop := by
      simpa only [sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-(a ^ (ν.re + 1))) (tendsto_rpow_atTop hp)
    have ht := (tendsto_div_const_atTop_of_pos hp).mpr hsub
    exact ht.congr' ((eventually_ge_atTop a).mono fun x hx => (hnormInt x hx).symm)
  have hFnorm : Tendsto (fun x : ℝ => ‖(x : ℂ) ^ (ν + 1) / (ν + 1)‖) atTop atTop := by
    have ht := (tendsto_div_const_atTop_of_pos (norm_pos_iff.mpr hn)).mpr
      (tendsto_rpow_atTop hp)
    refine ht.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun x hx => ?_)
    dsimp only
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, add_re, one_re]
  have hF : (fun x : ℝ => ∫ t in a..x, (t : ℂ) ^ ν) ~[atTop]
      fun x => (x : ℂ) ^ (ν + 1) / (ν + 1) := by
    have hb := Asymptotics.IsEquivalent.add_const_of_norm_tendsto_atTop
      (u := fun x : ℝ => (x : ℂ) ^ (ν + 1) / (ν + 1))
      (c := -(a : ℂ) ^ (ν + 1) / (ν + 1)) IsEquivalent.refl hFnorm
    refine hb.congr_left (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [integral_cpow (Or.inl hν)]
    ring
  have hO : (fun x : ℝ => ∫ t in a..x, ‖(t : ℂ) ^ ν‖) =O[atTop]
      fun x => (x : ℂ) ^ (ν + 1) / (ν + 1) := by
    refine IsBigO.of_bound (‖ν + 1‖ / (ν.re + 1)) ?_
    filter_upwards [eventually_ge_atTop a] with x hx
    have hpos : 0 ≤ ∫ t in a..x, ‖(t : ℂ) ^ ν‖ :=
      intervalIntegral.integral_nonneg_of_forall hx fun _ => norm_nonneg _
    rw [Real.norm_of_nonneg hpos, hnormInt x hx, norm_div,
      Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hx), add_re, one_re]
    calc (x ^ (ν.re + 1) - a ^ (ν.re + 1)) / (ν.re + 1) ≤
        x ^ (ν.re + 1) / (ν.re + 1) :=
      div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg ha.le _)) hp.le
      _ = ‖ν + 1‖ / (ν.re + 1) * (x ^ (ν.re + 1) / ‖ν + 1‖) := by
        field_simp
  exact h.intervalIntegral_of_integral_norm hf hg hF hO hG

/-- The tail integral of a bounded function times an integrable real power has
the order of the tail integral of that power. No regularity of the bounded
representative is needed for the bound on the totalized integral. -/
theorem isBigO_integral_Ioi_bdd_mul_rpow {f : ℝ → ℂ} {C r : ℝ}
    (hf : ∀ t, ‖f t‖ ≤ C) (hr : r < -1) :
    (fun x : ℝ => ∫ t in Ioi x, f t * ((t ^ r : ℝ) : ℂ)) =O[atTop]
      (fun x : ℝ => x ^ (r + 1)) := by
  refine IsBigO.of_bound (C / (-(r + 1))) ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
  calc
    ‖∫ t in Ioi x, f t * ((t ^ r : ℝ) : ℂ)‖ ≤ (∫ t in Ioi x, C * t ^ r) := by
      refine norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt hr hx).const_mul C) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hx.trans ht).le _)]
      exact mul_le_mul_of_nonneg_right (hf t) (Real.rpow_nonneg (hx.trans ht).le _)
    _ = C / (-(r + 1)) * x ^ (r + 1) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hr hx]
      rw [div_neg]
      ring

/-- A continuous function asymptotic to `1/x` has a primitive asymptotic to
`log x`; complex-valued errors are allowed. -/
theorem Asymptotics.IsEquivalent.intervalIntegral_inv {f : ℝ → ℂ} {a : ℝ}
    (h : f ~[atTop] fun x => (x : ℂ)⁻¹) (ha : 0 < a)
    (hf : ContinuousOn f (Ici a)) :
    (fun x => ∫ t in a..x, f t) ~[atTop] fun x => (Real.log x : ℂ) := by
  have hg : ContinuousOn (fun x : ℝ => (x : ℂ)⁻¹) (Ici a) := by
    intro x hx
    exact (Complex.continuous_ofReal.continuousAt.inv₀
      (Complex.ofReal_ne_zero.mpr (ha.trans_le hx).ne')).continuousWithinAt
  have hnormInt (x : ℝ) (hx : a ≤ x) :
      (∫ t in a..x, ‖(t : ℂ)⁻¹‖) = Real.log x - Real.log a := by
    have he : (∫ t in a..x, ‖(t : ℂ)⁻¹‖) = ∫ t in a..x, t⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hx] at ht
      dsimp only
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha.trans_le ht.1)]
    rw [he, integral_inv_of_pos ha (ha.trans_le hx),
      Real.log_div (ha.trans_le hx).ne' ha.ne']
  have hInt (x : ℝ) (hx : a ≤ x) :
      (∫ t in a..x, (t : ℂ)⁻¹) = ((Real.log x - Real.log a : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_inv]
    rw [intervalIntegral.integral_ofReal, integral_inv_of_pos ha (ha.trans_le hx),
      Real.log_div (ha.trans_le hx).ne' ha.ne']
  have hG : Tendsto (fun x => ∫ t in a..x, ‖(t : ℂ)⁻¹‖) atTop atTop := by
    have ht : Tendsto (fun x : ℝ => Real.log x - Real.log a) atTop atTop := by
      simpa only [sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-Real.log a) Real.tendsto_log_atTop
    exact ht.congr' ((eventually_ge_atTop a).mono fun x hx => (hnormInt x hx).symm)
  have hFnorm : Tendsto (fun x : ℝ => ‖(Real.log x : ℂ)‖) atTop atTop := by
    simpa only [Complex.norm_real, Function.comp_def] using
      tendsto_norm_atTop_atTop.comp Real.tendsto_log_atTop
  have hF : (fun x : ℝ => ∫ t in a..x, (t : ℂ)⁻¹) ~[atTop] fun x => (Real.log x : ℂ) := by
    have hb := Asymptotics.IsEquivalent.add_const_of_norm_tendsto_atTop
      (u := fun x : ℝ => (Real.log x : ℂ)) (c := -(Real.log a : ℂ))
      IsEquivalent.refl hFnorm
    refine hb.congr_left ((eventually_ge_atTop a).mono fun x hx => ?_)
    dsimp only
    rw [hInt x hx, Complex.ofReal_sub]
    ring
  have he : (fun x : ℝ => ∫ t in a..x, ‖(t : ℂ)⁻¹‖) =ᶠ[atTop]
      fun x => ‖∫ t in a..x, (t : ℂ)⁻¹‖ := by
    filter_upwards [eventually_ge_atTop a] with x hx
    have hp : 0 ≤ Real.log x - Real.log a := by
      rw [← hnormInt x hx]
      exact intervalIntegral.integral_nonneg_of_forall hx fun _ => norm_nonneg _
    rw [hnormInt x hx, hInt x hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  have hO := hF.isBigO.norm_left.congr' he.symm EventuallyEq.rfl
  exact h.intervalIntegral_of_integral_norm hf hg hF hO hG
