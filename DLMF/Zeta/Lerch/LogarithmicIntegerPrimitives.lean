/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Lerch.LogarithmicKernel
public import DLMFMathlib.Analysis.Complex.StarPrimitive

/-!
# Successive primitives for the integer-order Lerch expansion

Starting from the regularized order-zero function and a holomorphic order-one base,
normalized segment primitives produce the higher positive integer orders. Their constants
are Hurwitz zeta values; the order-one constant is zero. Consequently their Taylor series
omit exactly the coefficient at index `m - 1`, as in DLMF 25.14.3_2.
-/

@[expose] public noncomputable section
open Complex Set Filter MeasureTheory
open scoped Real Topology Nat

namespace DLMF.Zeta.LerchLogarithmic

/-- Normalized primitives with an order-one base `b` and Hurwitz-zeta constants. -/
def integerRegularized (a : ℂ) (b : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => regularized 0 a
  | 1 => b
  | n + 2 => fun w => hurwitzZetaComplex (n + 2) a +
      w * ∫ t in (0 : ℝ)..1, integerRegularized a b (n + 1) (t * w)

/-- The normalized primitives have the prescribed values at the origin. -/
theorem integerRegularized_zero {a : ℂ} (ha : 0 < a.re) {b : ℂ → ℂ} (hb : b 0 = 0)
    (n : ℕ) : integerRegularized a b n 0 =
      if n = 1 then 0 else hurwitzZetaComplex n a := by
  have hs0 : ∀ k : ℕ, (0 : ℂ) ≠ (k : ℂ) + 1 := by
    intro k h
    have hh := congrArg re h
    simp only [zero_re, add_re, natCast_re, one_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) k]
  rcases n with _ | _ | n
  · simp only [integerRegularized, Nat.zero_ne_one, ↓reduceIte, Nat.cast_zero]
    exact regularized_zero ha hs0
  · change b 0 = 0
    exact hb
  · have hn : n + 1 + 1 ≠ 1 := by omega
    simp only [hn, ↓reduceIte, integerRegularized, zero_mul, add_zero]
    congr 1
    push_cast
    ring

/-- All normalized primitives are holomorphic throughout the Hermite strip. -/
theorem differentiableOn_integerRegularized {a : ℂ} (ha : 0 < a.re) {b : ℂ → ℂ}
    (hb : ∀ w : ℂ, |w.im| < 2 * π → HasDerivAt b (regularized 0 a w) w) (n : ℕ) :
    DifferentiableOn ℂ (integerRegularized a b n) {w : ℂ | |w.im| < 2 * π} := by
  let U : Set ℂ := {w : ℂ | |w.im| < 2 * π}
  have hU : IsOpen U := isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  have hUc : Convex ℝ U := by
    convert (convex_halfSpace_im_gt (-(2 * π))).inter
      (convex_halfSpace_im_lt (2 * π)) using 1
    ext v
    simp [U, abs_lt]
  have h0 : (0 : ℂ) ∈ U := by simp [U]; positivity
  induction n using Nat.twoStepInduction with
  | zero =>
    intro w hw
    exact (hasDerivAt_regularized ha (by norm_num) hw).differentiableAt.differentiableWithinAt
  | one => exact fun w hw => (hb w hw).differentiableAt.differentiableWithinAt
  | more n _ ih =>
    intro w hw
    exact ((starPrim_hasDerivAt hU (hUc.starConvex h0) ih hw).const_add
      (hurwitzZetaComplex (n + 2) a)).differentiableAt.differentiableWithinAt

/-- Differentiating a positive-order primitive lowers its integer order by one. -/
theorem hasDerivAt_integerRegularized {a : ℂ} (ha : 0 < a.re) {b : ℂ → ℂ}
    (hb : ∀ w : ℂ, |w.im| < 2 * π → HasDerivAt b (regularized 0 a w) w)
    (n : ℕ) {w : ℂ} (hw : |w.im| < 2 * π) :
    HasDerivAt (integerRegularized a b (n + 1)) (integerRegularized a b n w) w := by
  rcases n with _ | n
  · exact hb w hw
  · have hU : IsOpen {v : ℂ | |v.im| < 2 * π} :=
      isOpen_lt (continuous_abs.comp continuous_im) continuous_const
    have hUc : Convex ℝ {v : ℂ | |v.im| < 2 * π} := by
      convert (convex_halfSpace_im_gt (-(2 * π))).inter
        (convex_halfSpace_im_lt (2 * π)) using 1
      ext v
      simp [abs_lt]
    have h0 : |(0 : ℂ).im| < 2 * π := by simp; positivity
    exact (starPrim_hasDerivAt hU (hUc.starConvex h0)
      (differentiableOn_integerRegularized ha hb (n + 1)) hw).const_add
        (hurwitzZetaComplex (n + 2) a)

/-- The derivatives at zero are Hurwitz-zeta values except for the omitted pole coefficient. -/
theorem iteratedDeriv_integerRegularized_zero {a : ℂ} (ha : 0 < a.re) {b : ℂ → ℂ}
    (hb0 : b 0 = 0)
    (hb : ∀ w : ℂ, |w.im| < 2 * π → HasDerivAt b (regularized 0 a w) w)
    (m n : ℕ) :
    iteratedDeriv n (integerRegularized a b m) 0 =
      if 0 < m ∧ n + 1 = m then 0 else hurwitzZetaComplex ((m : ℂ) - n) a := by
  have hs0 : ∀ k : ℕ, (0 : ℂ) ≠ (k : ℂ) + 1 := by
    intro k h
    have hh := congrArg re h
    simp only [zero_re, add_re, natCast_re, one_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) k]
  induction n generalizing m with
  | zero =>
    rw [iteratedDeriv_zero, integerRegularized_zero ha hb0]
    simp only [CharP.cast_eq_zero, sub_zero, zero_add]
    have he : (0 < m ∧ 1 = m) ↔ m = 1 := by omega
    simp only [he]
  | succ n ih =>
    rcases m with _ | m
    · rw [integerRegularized, iteratedDeriv_regularized ha (n + 1) hs0
        (by simp; positivity),
        regularized_zero ha (ne_natCast_add_one_sub_natCast hs0 (n + 1))]
      simp
    · rw [iteratedDeriv_succ']
      have heq : deriv (integerRegularized a b (m + 1)) =ᶠ[𝓝 (0 : ℂ)]
          integerRegularized a b m := by
        filter_upwards [(isOpen_lt (continuous_abs.comp continuous_im) continuous_const).mem_nhds
          (show |(0 : ℂ).im| < 2 * π by simp; positivity)] with w hw
        exact (hasDerivAt_integerRegularized ha hb m hw).deriv
      rw [heq.iteratedDeriv_eq n, ih]
      have he : (0 < m ∧ n + 1 = m) ↔ (0 < m + 1 ∧ n + 1 + 1 = m + 1) := by omega
      simp only [he]
      congr 2
      push_cast
      ring

/-- Taylor expansion of the normalized positive-order primitives with the pole term omitted. -/
theorem hasSum_integerRegularized {a : ℂ} (ha : 0 < a.re) {b : ℂ → ℂ} (hb0 : b 0 = 0)
    (hb : ∀ w : ℂ, |w.im| < 2 * π → HasDerivAt b (regularized 0 a w) w)
    {m : ℕ} (hm : 1 ≤ m) {w : ℂ} (hw : ‖w‖ < 2 * π) :
    HasSum (fun n : ℕ => if n = m - 1 then 0 else
      hurwitzZetaComplex ((m : ℂ) - n) a * w ^ n / n !)
      (integerRegularized a b m w) := by
  have hf : DifferentiableOn ℂ (integerRegularized a b m) (Metric.ball 0 (2 * π)) := by
    intro v hv
    have hv' : ‖v‖ < 2 * π := by simpa [Metric.mem_ball, dist_zero_right] using hv
    exact ((differentiableOn_integerRegularized ha hb m).differentiableAt
      ((isOpen_lt (continuous_abs.comp continuous_im) continuous_const).mem_nhds
        ((abs_im_le_norm v).trans_lt hv'))).differentiableWithinAt
  have h := Complex.hasSum_taylorSeries_on_ball hf
    (z := w) (by simpa [Metric.mem_ball, dist_zero_right] using hw)
  convert h using 1
  funext n
  rw [iteratedDeriv_integerRegularized_zero ha hb0 hb]
  simp only [sub_zero, smul_eq_mul]
  by_cases hn : n = m - 1
  · have he : 0 < m ∧ n + 1 = m := by omega
    rw [ite_eq_left hn, ite_eq_left he]
    simp
  · have he : ¬ (0 < m ∧ n + 1 = m) := by omega
    rw [ite_eq_right hn, ite_eq_right he]
    ring

end DLMF.Zeta.LerchLogarithmic
