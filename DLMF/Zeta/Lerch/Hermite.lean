/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Lerch.HermiteBounds
public import DLMF.Zeta.Lerch.HermiteInitial
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Hermite's representation of Lerch's transcendent

The Gamma–Laplace identity continues to every complex order and then throughout the
left half-strip of logarithmic arguments. Absolute convergence extends it to the unit
circle for `Re s > 1`. The ray integral is the limit of its finite interval integrals,
as in DLMF 25.14.6.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.Zeta.LerchHermite

/-- The Hermite identity for a negative real logarithmic argument holds at every order. -/
theorem lerchPhi_exp_eq_of_real {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : r < 0) (s : ℂ) :
    lerchPhi (exp (r : ℂ)) s a = a ^ (-s) / 2 +
      (∫ x in Ioi (0 : ℝ), rayKernel s a r x) +
      2 * ∫ y in Ioi (0 : ℝ), kernel s a r y := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hz : ‖exp (r : ℂ)‖ < 1 := by
    simpa only [norm_exp, ofReal_re] using Real.exp_lt_one_iff.mpr hr
  have hw : |((r : ℂ)).im| < 2 * π := by simp; positivity
  have hleft := differentiable_lerchPhi_order_of_norm_lt_one ha hz
  have hright : Differentiable ℂ (fun t : ℂ => a ^ (-t) / 2 +
      (∫ x in Ioi (0 : ℝ), rayKernel t a r x) +
      2 * ∫ y in Ioi (0 : ℝ), kernel t a r y) :=
    (((differentiable_id.neg.const_cpow (Or.inl ha0)).div_const 2).add
      (differentiable_integral_rayKernel_order ha (by simpa using hr))).add
      ((differentiable_integral_kernel_order ha hw).const_mul 2)
  have hf := hleft.differentiableOn.analyticOnNhd isOpen_univ
  have hg := hright.differentiableOn.analyticOnNhd isOpen_univ
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ
    (z₀ := 1) (mem_univ _) ?_ (mem_univ s)
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with t ht
  exact lerchPhi_exp_eq_of_real_pos_order ha ht hr

/-- The logarithmic Hermite representation holds on the open left half-strip. -/
theorem lerchPhi_exp_eq_of_re_neg {a w : ℂ} (ha : 0 < a.re) (hw0 : w.re < 0)
    (hw : |w.im| < 2 * π) (s : ℂ) :
    lerchPhi (exp w) s a = a ^ (-s) / 2 +
      (∫ x in Ioi (0 : ℝ), rayKernel s a w x) +
      2 * ∫ y in Ioi (0 : ℝ), kernel s a w y := by
  let U : Set ℂ := {v : ℂ | v.re < 0 ∧ -(2 * π) < v.im ∧ v.im < 2 * π}
  have hU : IsOpen U :=
    (isOpen_lt continuous_re continuous_const).inter
      ((isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const))
  have hconv : Convex ℝ U :=
    (convex_halfSpace_re_lt 0).inter
      ((convex_halfSpace_im_gt (-(2 * π))).inter (convex_halfSpace_im_lt (2 * π)))
  have h0 : (-1 : ℂ) ∈ U := by
    change (-1 : ℂ).re < 0 ∧ -(2 * π) < (-1 : ℂ).im ∧ (-1 : ℂ).im < 2 * π
    norm_num
    exact Real.pi_pos
  have hleft : DifferentiableOn ℂ (fun v => lerchPhi (exp v) s a) U := by
    intro v hv
    have hz : exp v ∈ slitOne := mem_slitOne_of_norm_lt_one (by
      rw [norm_exp]
      exact Real.exp_lt_one_iff.mpr hv.1)
    have hA := (analyticOnNhd_lerchPhi (lerchParamAdmissible_of_re_pos ha s) _ hz).differentiableAt
    exact (hA.comp v differentiableAt_id.cexp).differentiableWithinAt
  have hright : DifferentiableOn ℂ (fun v => a ^ (-s) / 2 +
      (∫ x in Ioi (0 : ℝ), rayKernel s a v x) +
      2 * ∫ y in Ioi (0 : ℝ), kernel s a v y) U := by
    intro v hv
    have hR := (differentiableOn_integral_rayKernel_argument ha s).differentiableAt
      ((isOpen_lt continuous_re continuous_const).mem_nhds hv.1)
    have hJ := (differentiableOn_integral_kernel_argument ha s).differentiableAt
      ((isOpen_lt (continuous_abs.comp continuous_im) continuous_const).mem_nhds
        (abs_lt.mpr hv.2))
    exact (((differentiableAt_const _).add hR).add (hJ.const_mul 2)).differentiableWithinAt
  refine (hleft.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq
    (hright.analyticOnNhd hU) hconv.isPreconnected h0 ?_ ⟨hw0, (abs_lt.mp hw).1, (abs_lt.mp hw).2⟩
  have hev : ∀ᶠ r : ℝ in 𝓝[≠] (-1),
      lerchPhi (exp (r : ℂ)) s a = a ^ (-s) / 2 +
        (∫ x in Ioi (0 : ℝ), rayKernel s a r x) +
        2 * ∫ y in Ioi (0 : ℝ), kernel s a r y := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 0))] with r hr
    exact lerchPhi_exp_eq_of_real ha hr s
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (-1)) (𝓝[≠] ((-1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      (fun r hr => Complex.ofReal_injective.ne hr)
  simpa only [Complex.ofReal_neg, Complex.ofReal_one] using
    (ht.frequently (p := fun v : ℂ => lerchPhi (exp v) s a = a ^ (-s) / 2 +
      (∫ x in Ioi (0 : ℝ), rayKernel s a v x) +
      2 * ∫ y in Ioi (0 : ℝ), kernel s a v y) hev.frequently)

/-- Absolute convergence extends the Hermite identity to the imaginary boundary. -/
theorem lerchPhi_exp_eq_of_re_eq_zero {a s w : ℂ} (ha : 0 < a.re) (hs : 1 < s.re)
    (hw0 : w.re = 0) (hw : |w.im| < 2 * π) :
    lerchPhi (exp w) s a = a ^ (-s) / 2 +
      (∫ x in Ioi (0 : ℝ), rayKernel s a w x) +
      2 * ∫ y in Ioi (0 : ℝ), kernel s a w y := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let u : ℕ → ℂ := fun n => w - (ε n : ℂ)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hu : Tendsto u atTop (𝓝 w) := by
    have h := continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [u, ε] using tendsto_const_nhds.sub h
  have hure (n : ℕ) : (u n).re < 0 := by simp only [u, sub_re, ofReal_re, hw0]; linarith [hε n]
  have huim (n : ℕ) : |(u n).im| < 2 * π := by simpa [u] using hw
  have hn (n : ℕ) : ‖exp (u n)‖ < 1 := by
    rw [norm_exp]; exact Real.exp_lt_one_iff.mpr (hure n)
  have hwz : ‖exp w‖ = 1 := by rw [norm_exp, hw0, Real.exp_zero]
  have hPhi : Tendsto (fun n => lerchPhi (exp (u n)) s a) atTop
      (𝓝 (lerchPhi (exp w) s a)) := by
    have hsum := (summable_one_div_add_natCast_cpow hs a).norm
    have ht := tendsto_tsum_of_dominated_convergence hsum
      (f := fun n k => exp (u n) ^ k / (a + (k : ℕ)) ^ s)
      (g := fun k : ℕ => exp w ^ k / (a + k) ^ s)
      (fun k => (continuous_exp.continuousAt.tendsto.comp hu).pow k |>.div_const _)
      (Eventually.of_forall fun n k => by
        rw [norm_div, norm_pow, norm_div, norm_one]
        exact div_le_div_of_nonneg_right
          (pow_le_one₀ (norm_nonneg _) (hn n).le) (norm_nonneg _))
    simp only [(hasSum_lerchPhi_of_norm_eq_one' hs hwz).tsum_eq] at ht
    exact ht.congr (fun n => (hasSum_lerchPhi
      (lerchParamAdmissible_of_re_pos ha s) (hn n)).tsum_eq)
  obtain ⟨g, hg, hb⟩ := exists_integrable_bound_rayKernel_boundary ha hs
  have hR : Tendsto (fun n => ∫ x in Ioi (0 : ℝ), rayKernel s a (u n) x) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), rayKernel s a w x)) := by
    refine tendsto_integral_of_dominated_convergence g
      (fun n => (continuousOn_rayKernel ha s (u n)).aestronglyMeasurable measurableSet_Ioi)
      hg (fun n => ?_) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hb (u n) (hure n).le x hx
    · exact Eventually.of_forall fun x =>
        (differentiable_rayKernel_argument a s x w).continuousAt.tendsto.comp hu
  have hJ : Tendsto (fun n => ∫ y in Ioi (0 : ℝ), kernel s a (u n) y) atTop
      (𝓝 (∫ y in Ioi (0 : ℝ), kernel s a w y)) := by
    have h := (differentiableOn_integral_kernel_argument ha s).differentiableAt
      ((isOpen_lt (continuous_abs.comp continuous_im) continuous_const).mem_nhds hw)
    exact h.continuousAt.tendsto.comp hu
  have hright := (hR.const_add (a ^ (-s) / 2)).add (hJ.const_mul (2 : ℂ))
  exact tendsto_nhds_unique hPhi (hright.congr fun n =>
    (lerchPhi_exp_eq_of_re_neg ha (hure n) (huim n) s).symm)

/-- The logarithmic Hermite representation implies the finite-interval limiting formula. -/
theorem tendsto_integral_hermite {z s a : ℂ} (ha : 0 < a.re)
    (h : (0 < ‖z‖ ∧ ‖z‖ < 1) ∨ (‖z‖ = 1 ∧ 1 < s.re)) :
    Tendsto (fun X : ℝ => a ^ (-s) / 2 + (∫ x in (0 : ℝ)..X, z ^ (x : ℂ) / (a + x) ^ s) -
        2 * ∫ x in Ioi (0 : ℝ), Complex.sin (x * Complex.log z - s * Complex.arctan (x / a)) /
          ((a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2) * (Real.exp (2 * π * x) - 1 : ℝ))) atTop
      (𝓝 (lerchPhi z s a)) := by
  have hz0 : z ≠ 0 := by
    intro hz
    rcases h with h | h <;> simp [hz] at h
  have hw : |(log z).im| < 2 * π := by
    rw [log_im]
    exact (abs_le.mpr ⟨(neg_pi_lt_arg z).le, arg_le_pi z⟩).trans_lt
      (by nlinarith [Real.pi_pos])
  have hI : IntegrableOn (rayKernel s a (log z)) (Ioi 0) := by
    rcases h with h | h
    · exact integrableOn_rayKernel_of_re_neg ha
        (by rw [log_re]; exact Real.log_neg (norm_pos_iff.mpr hz0) h.2) s
    · exact integrableOn_rayKernel_of_re_le_zero ha h.2 (by simp [log_re, h.1])
  have hPhi : lerchPhi z s a = a ^ (-s) / 2 +
      (∫ x in Ioi (0 : ℝ), rayKernel s a (log z) x) +
      2 * ∫ y in Ioi (0 : ℝ), kernel s a (log z) y := by
    rcases h with h | h
    · simpa only [exp_log hz0] using lerchPhi_exp_eq_of_re_neg ha
        (by rw [log_re]; exact Real.log_neg (norm_pos_iff.mpr hz0) h.2) hw s
    · simpa only [exp_log hz0] using
        lerchPhi_exp_eq_of_re_eq_zero ha h.2 (by simp [log_re, h.1]) hw
  have hRay (x : ℝ) : z ^ (x : ℂ) / (a + x) ^ s = rayKernel s a (log z) x := by
    rw [rayKernel, cpow_def_of_ne_zero hz0, cpow_neg, div_eq_mul_inv]
  have hK : (∫ x in Ioi (0 : ℝ), Complex.sin
      (x * Complex.log z - s * Complex.arctan (x / a)) /
      ((a ^ 2 + (x : ℂ) ^ 2) ^ (s / 2) * (Real.exp (2 * π * x) - 1 : ℝ))) =
      -(∫ x in Ioi (0 : ℝ), kernel s a (log z) x) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [kernel, ← neg_sub (s * arctan (x / a)) (x * log z), sin_neg]
    ring
  simp_rw [hRay]
  rw [hK]
  have ht := intervalIntegral_tendsto_integral_Ioi 0 hI tendsto_id
  convert (ht.const_add (a ^ (-s) / 2)).add_const
    (2 * ∫ x in Ioi (0 : ℝ), kernel s a (log z) x) using 1
  · funext X; simp only [id_eq]; ring
  · rw [hPhi]

end DLMF.Zeta.LerchHermite
