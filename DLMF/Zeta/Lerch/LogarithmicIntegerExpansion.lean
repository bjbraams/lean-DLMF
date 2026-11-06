/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Lerch.LogarithmicIntegerBase
public import DLMF.Zeta.Lerch.LogarithmicIntegerPrimitives
public import DLMF.Zeta.Lerch.LogarithmicIntegerBoundary

/-!
# The integer logarithmic expansion in the right half-plane

Normalized holomorphic primitives agree with the logarithmically corrected Lerch function
on the negative real axis. The derivative recurrence determines their differences up to a
constant, and the unit-circle limit fixes those constants. Continuation to the logarithmic
slit and Taylor expansion then give DLMF 25.14.3_2 for `Re a > 0`.
-/

@[expose] public noncomputable section
open Complex Set Filter MeasureTheory
open scoped Real Topology Nat

namespace DLMF.Zeta.LerchLogarithmic

/-- The normalized integer primitives equal the logarithmically corrected expression on the
negative real axis. -/
theorem integerRegularized_eq_of_real {a : ℂ} (ha : 0 < a.re) (n : ℕ) {r : ℝ} (hr : r < 0) :
    integerRegularized a (integerBase a) (n + 1) r = integerExpression a n r := by
  have ha' : ∀ k : ℕ, a + k ≠ 0 := by
    intro k hk
    have hh := congrArg re hk
    simp only [add_re, natCast_re, zero_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) k]
  induction n generalizing r with
  | zero =>
    simpa only [integerRegularized, integerExpression, CharP.cast_eq_zero, zero_add,
      pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul] using
        integerBase_eq_of_real ha hr
  | succ n ih =>
    let G : ℝ → ℂ := fun t => integerRegularized a (integerBase a) (n + 2) t -
      integerExpression a (n + 1) t
    have hd (t : ℝ) (ht : t < 0) : HasDerivAt G 0 t := by
      have hw : |((t : ℂ)).im| < 2 * π := by simp; positivity
      have hw' : -(t : ℂ) ∈ slitPlane := Or.inl (by simpa using neg_pos.mpr ht)
      have hP := (hasDerivAt_integerRegularized ha (fun w hw => hasDerivAt_integerBase ha hw)
        (n + 1) hw).comp_ofReal (z := t)
      have hE := (hasDerivAt_integerExpression_succ ha' hw hw' n).comp_ofReal (z := t)
      simpa only [G, Pi.sub_def, show n + 1 + 1 = n + 2 by omega, ih ht, sub_self]
        using hP.sub hE
    have hconst {t u : ℝ} (ht : t < 0) (hu : u < 0) : G t = G u :=
      isOpen_Iio.is_const_of_deriv_eq_zero isPreconnected_Iio
        (fun v hv => (hd v hv).differentiableAt.differentiableWithinAt)
        (fun v hv => (hd v hv).deriv) ht hu
    have hP : Tendsto (fun t : ℝ => integerRegularized a (integerBase a) (n + 2) t)
        (𝓝[<] 0) (𝓝 (hurwitzZetaComplex ((n : ℂ) + 2) a)) := by
      have h0 : |(0 : ℂ).im| < 2 * π := by simp; positivity
      have hD := (differentiableOn_integerRegularized ha
        (fun w hw => hasDerivAt_integerBase ha hw) (n + 2)).differentiableAt
          ((isOpen_lt (continuous_abs.comp continuous_im) continuous_const).mem_nhds h0)
      have hC := hD.continuousAt
      have hR : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[<] 0) (𝓝 0) :=
        (continuous_ofReal.continuousAt.tendsto (x := (0 : ℝ))).mono_left nhdsWithin_le_nhds
      have h := hC.tendsto.comp hR
      rw [integerRegularized_zero ha (integerBase_zero ha)] at h
      simpa only [show n + 2 ≠ 1 by omega, ↓reduceIte, Nat.cast_add, Nat.cast_ofNat,
        Function.comp_def] using h
    have hG : Tendsto G (𝓝[<] 0) (𝓝 0) := by
      simpa only [G, sub_self] using hP.sub (tendsto_integerExpression_succ_zero ha n)
    have hc : Tendsto G (𝓝[<] 0) (𝓝 (G r)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hconst hr ht
    exact sub_eq_zero.mp (tendsto_nhds_unique hc hG)

/-- Continuation of the integer primitive identity to the principal logarithmic slit strip. -/
theorem integerRegularized_succ_succ_eq {a w : ℂ} (ha : 0 < a.re) (n : ℕ)
    (hw : |w.im| < 2 * π) (hw' : -w ∈ slitPlane) :
    integerRegularized a (integerBase a) (n + 2) w = integerExpression a (n + 1) w := by
  let S : Set ℂ := {v : ℂ | -(2 * π) < v.im ∧ v.im < 2 * π}
  let U : Set ℂ := S ∩ (-slitPlane)
  have hS : IsOpen S :=
    (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have hU : IsOpen U := hS.inter isOpen_slitPlane.neg
  have hSc : Convex ℝ S :=
    (convex_halfSpace_im_gt (-(2 * π))).inter (convex_halfSpace_im_lt (2 * π))
  have hm : (-1 : ℂ) ∈ S := by
    change -(2 * π) < (-1 : ℂ).im ∧ (-1 : ℂ).im < 2 * π
    simp only [neg_im, one_im, neg_zero]
    constructor <;> nlinarith [Real.pi_pos]
  have hmU : (-1 : ℂ) ∈ U := ⟨hm, by simp⟩
  have hstar : StarConvex ℝ (-1 : ℂ) U :=
    (hSc.starConvex hm).inter starConvex_one_slitPlane.neg
  have ha' : ∀ k : ℕ, a + k ≠ 0 := by
    intro k hk
    have hh := congrArg re hk
    simp only [add_re, natCast_re, zero_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hf : DifferentiableOn ℂ (integerRegularized a (integerBase a) (n + 2)) U := by
    intro v hv
    have hD := (differentiableOn_integerRegularized ha
      (fun w hw => hasDerivAt_integerBase ha hw) (n + 2)).differentiableAt
        ((isOpen_lt (continuous_abs.comp continuous_im) continuous_const).mem_nhds
          (abs_lt.mpr hv.1))
    exact hD.differentiableWithinAt
  have hg : DifferentiableOn ℂ (integerExpression a (n + 1)) U := by
    intro v hv
    exact (hasDerivAt_integerExpression_succ ha' (abs_lt.mpr hv.1)
      (by simpa using hv.2) n).differentiableAt.differentiableWithinAt
  refine (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU)
    (hstar.isPathConnected hmU).isConnected.isPreconnected hmU ?_ ⟨abs_lt.mp hw, by simpa⟩
  have hev : ∀ᶠ r : ℝ in 𝓝[≠] (-1), integerRegularized a (integerBase a) (n + 2) r =
      integerExpression a (n + 1) r := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 0))] with r hr
    exact integerRegularized_eq_of_real ha (n + 1) hr
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (-1)) (𝓝[≠] ((-1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      (fun r hr => Complex.ofReal_injective.ne hr)
  simpa only [ofReal_neg, ofReal_one] using
    (ht.frequently (p := fun v : ℂ => integerRegularized a (integerBase a) (n + 2) v =
      integerExpression a (n + 1) v) hev.frequently)

/-- The integer logarithmic Lerch expansion in the right half-plane of its parameter. -/
theorem hasSum_lerchPhi_log_nat_of_re_pos {a : ℂ} (ha : 0 < a.re) {m : ℕ} (hm : 2 ≤ m)
    {z : ℂ} (hz : z ∈ slitOne) (hz0 : z ≠ 0) (hlog : ‖log z‖ < 2 * π) :
    HasSum (fun n : ℕ => if n = m - 1 then 0 else
        hurwitzZetaComplex ((m : ℂ) - n) a * log z ^ n / n !)
      (z ^ a * lerchPhi z m a - log z ^ (m - 1) / (m - 1)! *
        (digamma m - digamma a - log (-log z))) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hw : -log z ∈ slitPlane := by
    by_cases hI : (log z).im = 0
    · have harg : arg z = 0 := by simpa only [log_im] using hI
      have hp := arg_eq_zero_iff.mp harg
      have hR : z.re < 1 := hz.resolve_left (by simpa using hp.2)
      have heq : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hp.2)
      have hn : ‖z‖ < 1 := by
        rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp.1]
        exact hR
      exact Or.inl (by
        rw [neg_re, log_re]
        exact neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr hz0) hn))
    · exact Or.inr (by simpa only [neg_im, neg_ne_zero] using hI)
  have h := hasSum_integerRegularized ha (integerBase_zero ha)
    (fun w hw => hasDerivAt_integerBase ha hw) (m := n + 2) (by omega) hlog
  rw [integerRegularized_succ_succ_eq ha n ((abs_im_le_norm (log z)).trans_lt hlog) hw,
    integerExpression, exp_log hz0] at h
  simpa only [show n + 2 - 1 = n + 1 by omega, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    show (n : ℂ) + 1 + 1 = n + 2 by ring, cpow_def_of_ne_zero hz0,
    mul_comm a (log z)] using h

end DLMF.Zeta.LerchLogarithmic
