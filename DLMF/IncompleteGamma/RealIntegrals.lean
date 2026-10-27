/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Statistical.IncompleteGamma

/-!
# Real integral forms of the incomplete Gamma functions

For real parameter `a` and `x > 0` the upper and lower incomplete Gamma functions are real
integrals: `Γ(a,x) = ∫ₓ^∞ t^{a-1} e^{-t} dt` and, for `a > 0`, `γ(a,x) = ∫₀ˣ t^{a-1} e^{-t} dt`.
This file records these real forms together with the elementary pointwise comparisons behind
DLMF 8.10.1, 8.10.2 and 8.10.4 and the finite integration-by-parts expansion behind the
remainder bound of DLMF §8.11(i). Helper names carry the prefix `incG_`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open DLMF.Statistical

/-- Real form of `Γ(a,x) = ∫ₓ^∞ t^{a-1} e^{-t} dt` for real `a` and `x > 0`. -/
theorem incG_upperIncGamma_re_eq (a : ℝ) {x : ℝ} (hx : 0 < x) :
    (upperIncGamma a x).re = ∫ t in Ioi x, t^(a-1)*Real.exp (-t) := by
  rw [upperIncGamma_eq_integral (a:ℂ) hx]
  have : (∫ t in Ioi x, (t : ℂ) ^ ((a:ℂ) - 1) * Real.exp (-t)) =
      ((∫ t in Ioi x, t^(a-1)*Real.exp (-t) : ℝ) : ℂ) := by
    rw [show ((∫ t in Ioi x, t^(a-1)*Real.exp (-t) : ℝ) : ℂ) =
      ∫ t in Ioi x, ((t^(a-1)*Real.exp (-t) : ℝ) : ℂ) from integral_ofReal.symm]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := lt_trans hx ht
    push_cast
    rw [ofReal_cpow ht0.le]; push_cast; ring_nf
  rw [this, ofReal_re]

/-- Integrability of `t^{a-1} e^{-t}` on `(x,∞)` for `a ≤ 1` and `x > 0`. -/
theorem incG_integrableOn_rpow_exp_of_le_one {a : ℝ} (ha : a ≤ 1) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => t^(a-1)*Real.exp (-t)) (Ioi x) := by
  refine ((integrableOn_exp_neg_Ioi x).const_mul (x^(a-1))).mono' ?_ ?_
  · exact (ContinuousOn.mul (fun t ht => (Real.continuousAt_rpow_const _ _
      (Or.inl (lt_trans hx ht).ne')).continuousWithinAt) (Real.continuous_exp.comp
      continuous_neg).continuousOn).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0:ℝ) < t := lt_trans hx ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx (le_of_lt ht) (by linarith))
      (Real.exp_pos _).le

/-- Integrability of `t^{a-1} e^{-t}` on `(x,∞)` for `a > 0` and `x > 0`. -/
theorem incG_integrableOn_rpow_exp_of_pos {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => t^(a-1)*Real.exp (-t)) (Ioi x) := by
  have := (Real.GammaIntegral_convergent ha).mono_set (Ioi_subset_Ioi hx.le)
  refine this.congr_fun (fun t _ => by ring) measurableSet_Ioi

/-- `Γ(a,x) ≤ x^{a-1} e^{-x}` for real `a ≤ 1` (any sign) and `x > 0`. -/
theorem incG_upperIncGamma_re_le {a : ℝ} (ha : a ≤ 1) {x : ℝ} (hx : 0 < x) :
    (upperIncGamma a x).re ≤ x^(a-1)*Real.exp (-x) := by
  rw [incG_upperIncGamma_re_eq a hx, ← integral_exp_neg_Ioi, ← integral_const_mul]
  refine setIntegral_mono_on (incG_integrableOn_rpow_exp_of_le_one ha hx)
    ((integrableOn_exp_neg_Ioi x).const_mul _) measurableSet_Ioi fun t ht => ?_
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx (le_of_lt ht) (by linarith))
      (Real.exp_pos _).le

/-- `x^{a-1} e^{-x} ≤ Γ(a,x)` for real `a ≥ 1` and `x > 0`. -/
theorem incG_upperIncGamma_re_ge {a : ℝ} (ha : 1 ≤ a) {x : ℝ} (hx : 0 < x) :
    x^(a-1)*Real.exp (-x) ≤ (upperIncGamma a x).re := by
  rw [incG_upperIncGamma_re_eq a hx, ← integral_exp_neg_Ioi, ← integral_const_mul]
  refine setIntegral_mono_on ((integrableOn_exp_neg_Ioi x).const_mul _)
    (incG_integrableOn_rpow_exp_of_pos (by linarith) hx) measurableSet_Ioi fun t ht => ?_
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx.le (le_of_lt ht) (by linarith))
      (Real.exp_pos _).le

/-- Positivity of the real upper incomplete Gamma function when its integral converges. -/
theorem incG_upperIncGamma_re_pos {a : ℝ} {x : ℝ} (hx : 0 < x)
    (hi : IntegrableOn (fun t => t^(a-1)*Real.exp (-t)) (Ioi x)) :
    0 < (upperIncGamma a x).re := by
  rw [incG_upperIncGamma_re_eq a hx]
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hi]
  · have : Function.support (fun t : ℝ => t^(a-1)*Real.exp (-t)) ∩ Ioi x = Ioi x := by
      refine inter_eq_right.mpr fun t ht => ?_
      have ht0 : (0:ℝ) < t := lt_trans hx ht
      exact (mul_pos (Real.rpow_pos_of_pos ht0 _) (Real.exp_pos _)).ne'
    rw [this]; simp
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0:ℝ) < t := lt_trans hx ht
    exact (mul_pos (Real.rpow_pos_of_pos ht0 _) (Real.exp_pos _)).le

/-- Real form of `γ(a,x) = ∫₀ˣ t^{a-1} e^{-t} dt` for `a > 0`, `x > 0`. -/
theorem incG_lowerIncGamma_re_eq {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    (lowerIncGamma a x).re = ∫ t in (0:ℝ)..x, t^(a-1)*Real.exp (-t) := by
  rw [lowerIncGamma_eq_integral (by simpa using ha) hx]
  have : (∫ t in (0:ℝ)..x, (t : ℂ) ^ ((a:ℂ) - 1) * Real.exp (-t)) =
      ((∫ t in (0:ℝ)..x, t^(a-1)*Real.exp (-t) : ℝ) : ℂ) := by
    rw [show ((∫ t in (0:ℝ)..x, t^(a-1)*Real.exp (-t) : ℝ) : ℂ) =
      ∫ t in (0:ℝ)..x, ((t^(a-1)*Real.exp (-t) : ℝ) : ℂ) from intervalIntegral.integral_ofReal.symm]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht0 : (0:ℝ) ≤ t := by
      rw [uIcc_of_le hx.le] at ht; exact ht.1
    push_cast
    rw [ofReal_cpow ht0]; push_cast; ring_nf
  rw [this, ofReal_re]

/-- `∫₀ˣ t e^{-t} dt = 1-(1+x)e^{-x}`. -/
theorem incG_integral_mul_exp_neg (x : ℝ) :
    ∫ t in (0:ℝ)..x, t*Real.exp (-t) = 1-(1+x)*Real.exp (-x) := by
  have hd : ∀ t ∈ uIcc (0:ℝ) x, HasDerivAt (fun t => -(1+t)*Real.exp (-t)) (t*Real.exp (-t)) t := by
    intro t _
    have hA : HasDerivAt (fun t:ℝ => -(1+t)) (-1) t := by
      have := ((hasDerivAt_id t).const_add 1).neg
      exact this
    have hB : HasDerivAt (fun t:ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    convert hA.mul hB using 1; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  simp; ring

/-- The two-sided comparison behind DLMF 8.10.2. -/
theorem incG_lowerIncGamma_compare {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    a*(lowerIncGamma a x).re = (∫ t in (0:ℝ)..x, t^a*Real.exp (-t)) + x^a*Real.exp (-x) ∧
    x^(a-1)*(1-Real.exp (-x)) = (∫ t in (0:ℝ)..x, x^(a-1)*(t*Real.exp (-t))) + x^a*Real.exp (-x) := by
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have ha' : ∀ k : ℕ, (a:ℂ) ≠ -k := fun k hk => by
    have := congrArg Complex.re hk; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  constructor
  · have h := lowerIncGamma_add_one ha' hx0
    have hr := incG_lowerIncGamma_re_eq (a := a+1) (by linarith) hx
    push_cast at hr
    rw [h, add_sub_cancel_right] at hr
    have e : ((x:ℂ)^(a:ℂ)*exp (-(x:ℂ))).re = x^a*Real.exp (-x) := by
      rw [← ofReal_cpow hx.le, ← ofReal_neg, ← ofReal_exp, ← ofReal_mul, ofReal_re]
    rw [sub_re, e, show ((a:ℂ)*lowerIncGamma a x).re = a*(lowerIncGamma a x).re by simp] at hr
    linarith
  · rw [intervalIntegral.integral_const_mul, incG_integral_mul_exp_neg]
    have : x^a = x^(a-1)*x := by
      rw [← Real.rpow_add_one hx.ne']; ring_nf
    rw [this]; ring

/-- DLMF 8.10.2 for `0 < a ≤ 1`. -/
theorem incG_lowerIncGamma_bound_ge {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 < x) :
    (lowerIncGamma a x).re ≥ x^(a-1)/a*(1-Real.exp (-x)) := by
  obtain ⟨h1, h2⟩ := incG_lowerIncGamma_compare ha hx
  have hm : (∫ t in (0:ℝ)..x, x^(a-1)*(t*Real.exp (-t))) ≤ ∫ t in (0:ℝ)..x, t^a*Real.exp (-t) := by
    refine intervalIntegral.integral_mono_on hx.le (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; exact (Real.continuous_rpow_const ha.le).mul (by fun_prop))
      fun t ht => ?_
    rcases ht.1.eq_or_lt with h0 | h0
    · subst h0; simp [Real.zero_rpow ha.ne']
    · rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have : t^a = t^(a-1)*t := by rw [← Real.rpow_add_one h0.ne']; ring_nf
      rw [this]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos h0 ht.2 (by linarith)) h0.le
  rw [ge_iff_le, div_mul_eq_mul_div, div_le_iff₀ ha]
  linarith

/-- DLMF 8.10.2 reversed for `a ≥ 1`. -/
theorem incG_lowerIncGamma_bound_le {a x : ℝ} (ha : 1 ≤ a) (hx : 0 < x) :
    (lowerIncGamma a x).re ≤ x^(a-1)/a*(1-Real.exp (-x)) := by
  have ha0 : 0 < a := by linarith
  obtain ⟨h1, h2⟩ := incG_lowerIncGamma_compare ha0 hx
  have hm : (∫ t in (0:ℝ)..x, t^a*Real.exp (-t)) ≤ ∫ t in (0:ℝ)..x, x^(a-1)*(t*Real.exp (-t)) := by
    refine intervalIntegral.integral_mono_on hx.le
      (by apply Continuous.intervalIntegrable; exact (Real.continuous_rpow_const ha0.le).mul (by fun_prop))
      (by apply Continuous.intervalIntegrable; fun_prop)
      fun t ht => ?_
    rcases ht.1.eq_or_lt with h0 | h0
    · subst h0; simp [Real.zero_rpow ha0.ne']
    · rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have : t^a = t^(a-1)*t := by rw [← Real.rpow_add_one h0.ne']; ring_nf
      rw [this]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow h0.le ht.2 (by linarith)) h0.le
  rw [div_mul_eq_mul_div, le_div_iff₀ ha0]
  linarith

/-- `N` integrations by parts: `Γ(a,z) = ∑_{k<N} (-1)^k (1-a)_k z^{a-1-k} e^{-z}
+ (-1)^N (1-a)_N Γ(a-N,z)`. -/
theorem incG_upperIncGamma_expansion (a : ℂ) {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    upperIncGamma a z = (∑ k ∈ Finset.range N, (-1:ℂ)^k*poch (1-a) k*(z^(a-1-k)*exp (-z))) +
      (-1:ℂ)^N*poch (1-a) N*upperIncGamma (a-N) z := by
  induction N with
  | zero => simp [poch]
  | succ N ih =>
    have h := upperIncGamma_add_one (a-N-1) hz
    rw [show a-N-1+1 = a-N by ring] at h
    rw [ih, h, Finset.sum_range_succ, add_assoc]
    congr 1
    rw [poch_succ]
    push_cast
    ring_nf

/-- Real form: for real `b` and `x > 0`, `Γ(b,x)` is the real number `Re Γ(b,x)`. -/
theorem incG_upperIncGamma_ofReal_re (b : ℝ) {x : ℝ} (hx : 0 < x) :
    upperIncGamma b x = ((upperIncGamma b x).re : ℂ) := by
  rw [incG_upperIncGamma_re_eq b hx, upperIncGamma_eq_integral (b:ℂ) hx]
  rw [show ((∫ t in Ioi x, t^(b-1)*Real.exp (-t) : ℝ) : ℂ) =
      ∫ t in Ioi x, ((t^(b-1)*Real.exp (-t) : ℝ) : ℂ) from integral_ofReal.symm]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0:ℝ) < t := lt_trans hx ht
  push_cast
  rw [ofReal_cpow ht0.le]; push_cast; ring_nf

end DLMF.Confluent
