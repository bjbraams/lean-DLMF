/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Integral.PrincipalValueExcision
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
/-!
# The logarithmic kernel of a principal value on a half-line

Subtracting `(t+1)⁻¹` makes `(t-c)⁻¹` integrable at infinity. Removing its
singular part on `[c/2,3c/2]` gives an integrable function with integral `-log c`.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace MeasureTheory
private def logarithmicPrincipalValueKernel (c t : ℝ) : ℝ :=
  (t - c)⁻¹ - (t + 1)⁻¹ - (Icc (c / 2) (3 * c / 2)).indicator (fun t => (t - c)⁻¹) t
private lemma integral_logarithmicPrincipalValueKernel {c : ℝ} (hc : 0 < c) :
    IntegrableOn (logarithmicPrincipalValueKernel c) (Ioi 0) ∧
      ∫ t in Ioi 0, logarithmicPrincipalValueKernel c t = -Real.log c := by
  let a := c / 2
  let b := 3 * c / 2
  let B : ℝ → ℝ := fun t => (t - c)⁻¹ - (t + 1)⁻¹
  let L : ℝ → ℝ := fun t => Real.log (t - c) - Real.log (t + 1)
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hac : a < c := by dsimp [a]; linarith
  have hcb : c < b := by dsimp [b]; linarith
  have hab : a < b := hac.trans hcb
  have hBd (t : ℝ) (h1 : t - c ≠ 0) (h2 : t + 1 ≠ 0) : HasDerivAt L (B t) t := by
    convert (((hasDerivAt_id t).sub_const c).log h1).sub
      (((hasDerivAt_id t).add_const 1).log h2) using 1
    · funext s; rfl
    · simp [B]
  have hlim : Tendsto L atTop (𝓝 0) := by
    have hs : Tendsto (fun t : ℝ => (c + 1) / (t + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_id)
    have hr := (tendsto_const_nhds (x := (1 : ℝ))).sub hs
    simp only [sub_zero] at hr
    have H := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
    simp only [Real.log_one] at H
    apply H.congr'
    filter_upwards [eventually_gt_atTop c] with t ht
    dsimp [L]
    have h2 : t + 1 ≠ 0 := by linarith
    rw [show 1 - (c + 1) / (t + 1) = (t - c) / (t + 1) by field_simp; ring,
      Real.log_div (by linarith) h2]
  have htaild : ∀ t ∈ Ici b, HasDerivAt L (B t) t := by
    intro t ht
    change b ≤ t at ht
    apply hBd <;> linarith
  have htailpos : ∀ t ∈ Ioi b, 0 ≤ B t := by
    intro t ht
    change b < t at ht
    have h1 : 0 < t - c := by linarith
    have h2 : 0 < t + 1 := by linarith
    dsimp [B]
    exact sub_nonneg.mpr (inv_anti₀ h1 (by linarith))
  have hiT := integrableOn_Ioi_deriv_of_nonneg' htaild htailpos hlim
  have hIT := integral_Ioi_of_hasDerivAt_of_nonneg' htaild htailpos hlim
  have hAc : ContinuousOn B (Icc 0 a) := by
    change ContinuousOn (fun t : ℝ => (t - c)⁻¹ - (t + 1)⁻¹) (Icc 0 a)
    exact ((continuousOn_id.sub continuousOn_const).inv₀
      (fun t ht => by change t - c ≠ 0; linarith [ht.2])).sub
      ((continuousOn_id.add continuousOn_const).inv₀
        (fun t ht => by change t + 1 ≠ 0; linarith [ht.1]))
  have hiA : IntegrableOn B (Icc 0 a) := hAc.integrableOn_Icc
  have hIA : ∫ t in Ioo 0 a, B t = L a - L 0 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha0.le]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha0.le
    · intro t ht
      exact (hBd t (by linarith [ht.2]) (by linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht
      apply hBd <;> linarith [ht.1, ht.2]
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le ha0.le]; exact hiA
  have hMc : ContinuousOn (fun t : ℝ => -(t + 1)⁻¹) (Icc a b) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    linarith [ht.1]
  have hiM : IntegrableOn (fun t : ℝ => -(t + 1)⁻¹) (Icc a b) := hMc.integrableOn_Icc
  have hIM : ∫ t in Icc a b, -(t + 1)⁻¹ = -Real.log (b + 1) + Real.log (a + 1) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
    have hdM (t : ℝ) (ht : t ∈ Icc a b) :
        HasDerivAt (fun t : ℝ => -Real.log (t + 1)) (-(t + 1)⁻¹) t := by
      have H := (((hasDerivAt_id t).add_const 1).log
        (show id t + 1 ≠ 0 by simp only [id_eq]; linarith [ht.1])).neg
      convert H using 1
      · funext s; rfl
      · simp
    have H := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le
      (fun t ht => (hdM t ht).continuousAt.continuousWithinAt)
      (fun t ht => hdM t (Ioo_subset_Icc_self ht))
      (show IntervalIntegrable (fun t : ℝ => -(t + 1)⁻¹) volume a b by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]; exact hiM)
    convert H using 1; ring
  have eA : ∀ t ∈ Ioo 0 a, logarithmicPrincipalValueKernel c t = B t := by
    intro t ht
    dsimp [logarithmicPrincipalValueKernel, a] at *
    rw [indicator_of_notMem (by intro h; linarith [ht.2, h.1])]
    simp [B]
  have eM : ∀ t ∈ Icc a b, logarithmicPrincipalValueKernel c t = -(t + 1)⁻¹ := by
    intro t ht
    dsimp [logarithmicPrincipalValueKernel]
    rw [indicator_of_mem ht]
    ring
  have eT : ∀ t ∈ Ioi b, logarithmicPrincipalValueKernel c t = B t := by
    intro t ht
    change b < t at ht
    dsimp [logarithmicPrincipalValueKernel, b] at *
    rw [indicator_of_notMem (by intro h; linarith [ht, h.2])]
    simp [B]
  have hiAK := (hiA.mono_set Ioo_subset_Icc_self).congr_fun
    (fun t ht => (eA t ht).symm) measurableSet_Ioo
  have hiMK := hiM.congr_fun (fun t ht => (eM t ht).symm) measurableSet_Icc
  have hiTK := hiT.congr_fun (fun t ht => (eT t ht).symm) measurableSet_Ioi
  have hset : Ioi (0 : ℝ) = (Ioo 0 a ∪ Icc a b) ∪ Ioi b := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioo, mem_Icc]
    constructor
    · intro ht
      rcases lt_or_ge t a with h | h
      · exact Or.inl (Or.inl ⟨ht, h⟩)
      · rcases le_or_gt t b with h' | h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
        · exact Or.inr h'
    · rintro ((h | h) | h)
      · exact h.1
      · linarith [h.1]
      · linarith
  have hd1 : Disjoint (Ioo (0 : ℝ) a) (Icc a b) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    linarith [h1.2, h2.1]
  have hd2 : Disjoint (Ioo (0 : ℝ) a ∪ Icc a b) (Ioi b) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    change b < t at h2
    rcases h1 with h1 | h1 <;> linarith [h1.2]
  constructor
  · rw [hset]
    exact (hiAK.union hiMK).union hiTK
  · rw [hset, setIntegral_union hd2 measurableSet_Ioi (hiAK.union hiMK) hiTK,
      setIntegral_union hd1 measurableSet_Icc hiAK hiMK,
      setIntegral_congr_fun measurableSet_Ioo eA, setIntegral_congr_fun measurableSet_Icc eM,
      setIntegral_congr_fun measurableSet_Ioi eT, hIA, hIM, hIT]
    dsimp [L]
    rw [show a - c = -(b - c) by dsimp [a, b]; ring, Real.log_neg_eq_log]
    simp only [zero_sub, Real.log_neg_eq_log, zero_add, Real.log_one]
    ring
/-- The logarithmic principal-value kernel has an integrable regular part on `(0,∞)`. -/
theorem integrableOn_inv_sub_inv_add_sub_indicator {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (t - c)⁻¹ - (t + 1)⁻¹ -
      (Icc (c / 2) (3 * c / 2)).indicator (fun t => (t - c)⁻¹) t) (Ioi 0) :=
  (integral_logarithmicPrincipalValueKernel hc).1

/-- The logarithmic principal-value kernel has integral `-log c` on `(0,∞)`. -/
theorem integral_inv_sub_inv_add_sub_indicator {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), (t - c)⁻¹ - (t + 1)⁻¹ -
      (Icc (c / 2) (3 * c / 2)).indicator (fun t => (t - c)⁻¹) t = -Real.log c :=
  (integral_logarithmicPrincipalValueKernel hc).2

private lemma complex_logarithmicPrincipalValueKernel (c t : ℝ) :
    ((t : ℂ) - c)⁻¹ - ((t : ℂ) + 1)⁻¹ -
        (Icc (c / 2) (3 * c / 2)).indicator (fun t : ℝ => ((t : ℂ) - c)⁻¹) t =
      (logarithmicPrincipalValueKernel c t : ℂ) := by
  by_cases ht : t ∈ Icc (c / 2) (3 * c / 2)
  · simp only [logarithmicPrincipalValueKernel, indicator_of_mem ht]
    push_cast
    rfl
  · simp only [logarithmicPrincipalValueKernel, indicator_of_notMem ht]
    push_cast
    rfl

/-- Complex-valued form of the integrable logarithmic principal-value kernel. -/
theorem integrableOn_complex_inv_sub_inv_add_sub_indicator {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => ((t : ℂ) - c)⁻¹ - ((t : ℂ) + 1)⁻¹ -
      (Icc (c / 2) (3 * c / 2)).indicator (fun t : ℝ => ((t : ℂ) - c)⁻¹) t) (Ioi 0) := by
  simp_rw [complex_logarithmicPrincipalValueKernel]
  exact (integral_logarithmicPrincipalValueKernel hc).1.ofReal

/-- Complex-valued evaluation of the logarithmic principal-value kernel. -/
theorem integral_complex_inv_sub_inv_add_sub_indicator {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), ((t : ℂ) - c)⁻¹ - ((t : ℂ) + 1)⁻¹ -
      (Icc (c / 2) (3 * c / 2)).indicator (fun t : ℝ => ((t : ℂ) - c)⁻¹) t =
        (-Real.log c : ℝ) := by
  simp_rw [complex_logarithmicPrincipalValueKernel]
  rw [integral_complex_ofReal, (integral_logarithmicPrincipalValueKernel hc).2]

private lemma integral_inv_add_sub_inv_add_pos {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => (t + p)⁻¹ - (t + 1)⁻¹) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), (t + p)⁻¹ - (t + 1)⁻¹ = -Real.log p := by
  let L : ℝ → ℝ := fun t => Real.log (t + p) - Real.log (t + 1)
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt L ((t + p)⁻¹ - (t + 1)⁻¹) t := by
    intro t ht
    change 0 ≤ t at ht
    have H := (((hasDerivAt_id t).add_const p).log
      (show id t + p ≠ 0 by simp only [id_eq]; positivity)).sub
      (((hasDerivAt_id t).add_const 1).log
        (show id t + 1 ≠ 0 by simp only [id_eq]; positivity))
    convert H using 1
    · funext s; rfl
    · simp
  have hlim : Tendsto L atTop (𝓝 0) := by
    have hs : Tendsto (fun t : ℝ => (p - 1) / (t + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_id)
    have hr := (tendsto_const_nhds (x := (1 : ℝ))).add hs
    simp only [add_zero] at hr
    have H := (Real.continuousAt_log one_ne_zero).tendsto.comp hr
    simp only [Real.log_one] at H
    apply H.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp [L]
    rw [show 1 + (p - 1) / (t + 1) = (t + p) / (t + 1) by field_simp; ring,
      Real.log_div (by positivity) (by positivity)]
  rcases le_total p 1 with hp1 | h1p
  · have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ (t + p)⁻¹ - (t + 1)⁻¹ := by
      intro t ht
      change 0 < t at ht
      exact sub_nonneg.mpr (inv_anti₀ (by positivity) (by linarith))
    refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim, ?_⟩
    simpa only [L, zero_add, Real.log_one, sub_zero, zero_sub] using
      integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos hlim
  · have hneg : ∀ t ∈ Ioi (0 : ℝ), (t + p)⁻¹ - (t + 1)⁻¹ ≤ 0 := by
      intro t ht
      change 0 < t at ht
      exact sub_nonpos.mpr (inv_anti₀ (by positivity) (by linarith))
    refine ⟨integrableOn_Ioi_deriv_of_nonpos' hd hneg hlim, ?_⟩
    simpa only [L, zero_add, Real.log_one, sub_zero, zero_sub] using
      integral_Ioi_of_hasDerivAt_of_nonpos' hd hneg hlim

/-- The difference of two reciprocal linear kernels is integrable on the positive ray. -/
theorem integrableOn_inv_add_sub_inv_add {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => (t + p)⁻¹ - (t + 1)⁻¹) (Ioi 0) :=
  (integral_inv_add_sub_inv_add_pos hp).1

/-- The integral of the difference of two reciprocal linear kernels is `-log p`. -/
theorem integral_inv_add_sub_inv_add {p : ℝ} (hp : 0 < p) :
    ∫ t in Ioi (0 : ℝ), (t + p)⁻¹ - (t + 1)⁻¹ = -Real.log p :=
  (integral_inv_add_sub_inv_add_pos hp).2

private lemma complex_inv_add_sub_inv_add (p t : ℝ) :
    ((t : ℂ) + p)⁻¹ - ((t : ℂ) + 1)⁻¹ = (((t + p)⁻¹ - (t + 1)⁻¹ : ℝ) : ℂ) := by
  push_cast
  rfl

/-- Complex-valued integrability of the difference of two reciprocal linear kernels. -/
theorem integrableOn_complex_inv_add_sub_inv_add {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => ((t : ℂ) + p)⁻¹ - ((t : ℂ) + 1)⁻¹) (Ioi 0) := by
  simp_rw [complex_inv_add_sub_inv_add]
  exact (integral_inv_add_sub_inv_add_pos hp).1.ofReal

/-- Complex-valued evaluation of the difference of two reciprocal linear kernels. -/
theorem integral_complex_inv_add_sub_inv_add {p : ℝ} (hp : 0 < p) :
    ∫ t in Ioi (0 : ℝ), ((t : ℂ) + p)⁻¹ - ((t : ℂ) + 1)⁻¹ = (-Real.log p : ℝ) := by
  simp_rw [complex_inv_add_sub_inv_add]
  rw [integral_complex_ofReal, (integral_inv_add_sub_inv_add_pos hp).2]

end MeasureTheory

namespace Real

/-- Translating the argument of a logarithm does not change its leading behavior at infinity. -/
theorem tendsto_log_add_sub_log_add_atTop (a b : ℝ) :
    Tendsto (fun t : ℝ => Real.log (t + a) - Real.log (t + b)) atTop (𝓝 0) := by
  have hs : Tendsto (fun t : ℝ => (a - b) / (t + b)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ b tendsto_id)
  have hr := (tendsto_const_nhds (x := (1 : ℝ))).add hs
  simp only [add_zero] at hr
  have H := (Real.continuousAt_log one_ne_zero).tendsto.comp hr
  simp only [Real.log_one] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (max (-a) (-b))] with t ht
  have ha : t + a ≠ 0 := by linarith [le_max_left (-a) (-b)]
  have hb : t + b ≠ 0 := by linarith [le_max_right (-a) (-b)]
  change Real.log (1 + (a - b) / (t + b)) = _
  rw [show 1 + (a - b) / (t + b) = (t + a) / (t + b) by field_simp; ring,
    Real.log_div ha hb]

end Real
