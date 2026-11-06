/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Polylog.Properties
public import DLMF.Zeta.Basic.HurwitzProperties
public import DLMFMathlib.Analysis.Complex.IdentityTheoremStrip
public import Mathlib.NumberTheory.LSeries.HurwitzZeta

/-!
# Inversion of the principal polylogarithm

The branch-corrected inversion formula of DLMF 25.12.13 follows from the Hurwitz functional
equation on the unit circle, analytic continuation in the vertical strip, and the derivative
recurrence for the polylogarithm.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory
open scoped Nat Real Topology

namespace DLMF.Zeta

namespace PolylogInversion

/-- The combination of opposite exponential parameters in the inversion formula. -/
def combination (s w : ℂ) : ℂ :=
  polylog s (exp (2 * π * I * w)) + exp (π * I * s) *
    polylog s (exp (-(2 * π * I * w)))

/-- The Gamma-normalized coefficient in the polylogarithm inversion formula. -/
def coefficient (s : ℂ) : ℂ :=
  (2 * π) ^ s * exp (π * I * s / 2) / Gamma s

/-- The exponential parameter of a point in the open unit strip avoids the
principal polylogarithm cut. -/
theorem exp_mem_slitOne {w : ℂ} (hw : 0 < w.re ∧ w.re < 1) :
    exp (2 * π * I * w) ∈ slitOne := by
  by_cases hi : (exp (2 * π * I * w)).im ≠ 0
  · exact Or.inl hi
  · right
    have harg : (2 * π * I * w).im = 2 * π * w.re := by simp [mul_im, mul_re]
    have hs : Real.sin (2 * π * w.re) = 0 := by
      have h := not_ne_iff.mp hi
      rw [exp_im, harg] at h
      exact (mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero _)
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
    have hk0 : (0 : ℝ) < k := by nlinarith [Real.pi_pos, hw.1]
    have hk2 : (k : ℝ) < 2 := by nlinarith [Real.pi_pos, hw.2]
    have hk1 : k = 1 := by
      have : (0 : ℤ) < k := by exact_mod_cast hk0
      have : k < (2 : ℤ) := by exact_mod_cast hk2
      omega
    have hc : Real.cos (2 * π * w.re) = -1 := by
      rw [← hk, hk1]; norm_num
    change (exp (2 * π * I * w)).re < 1
    rw [exp_re, harg, hc]
    linarith [Real.exp_pos (2 * π * I * w).re]

/-- Reflection across the midpoint of the unit strip gives the inverse exponential. -/
theorem exp_one_sub (w : ℂ) :
    exp (2 * π * I * (1 - w)) = exp (-(2 * π * I * w)) := by
  rw [show 2 * π * I * (1 - w) = 2 * π * I + -(2 * π * I * w) by ring,
    exp_add, exp_two_pi_mul_I, one_mul]

/-- The reflected exponential also avoids the principal polylogarithm cut. -/
theorem exp_neg_mem_slitOne {w : ℂ} (hw : 0 < w.re ∧ w.re < 1) :
    exp (-(2 * π * I * w)) ∈ slitOne := by
  rw [← exp_one_sub]
  exact exp_mem_slitOne (by simp only [sub_re, one_re]; constructor <;> linarith [hw.1, hw.2])

/-- Hurwitz's functional equation on the open unit strip, initially for absolutely
convergent polylogarithm orders. -/
theorem eq_on_strip_of_one_lt_re {s : ℂ} (hs : 1 < s.re) {w : ℂ}
    (hw : 0 < w.re ∧ w.re < 1) :
    polylog s (exp (2 * π * I * w)) + exp (π * I * s) *
      polylog s (exp (-(2 * π * I * w))) =
        (2 * π) ^ s * exp (π * I * s / 2) / Gamma s *
          hurwitzZetaComplex (1 - s) w := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  have hs1 : 1 - s ≠ 1 := by simpa using hs0
  refine eqOn_strip_of_eq_ofReal (f := fun w =>
    polylog s (exp (2 * π * I * w)) + exp (π * I * s) *
      polylog s (exp (-(2 * π * I * w))))
    (g := fun w => (2 * π) ^ s * exp (π * I * s / 2) / Gamma s *
      hurwitzZetaComplex (1 - s) w) ?_ ?_ ?_ hw
  · intro v hv
    exact (((analyticOnNhd_polylog s _ (exp_mem_slitOne hv)).differentiableAt.comp v
      ((differentiableAt_id.const_mul _).cexp)).add
      (((analyticOnNhd_polylog s _ (exp_neg_mem_slitOne hv)).differentiableAt.comp v
        ((differentiableAt_id.const_mul _).neg.cexp)).const_mul _)).differentiableWithinAt
  · intro v hv
    have h := (differentiableOn_hurwitzZetaComplex_param' hs1).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hv.1)
    exact (h.const_mul _).differentiableWithinAt
  · intro x hx0 hx1
    have hsN : ∀ n : ℕ, s ≠ -n := fun n h => by
      have h' := congrArg Complex.re h
      simp only [neg_re, natCast_re] at h'
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have h := HurwitzZeta.hurwitzZeta_one_sub (x : UnitAddCircle) hsN (Or.inr (by
      intro h; simp [h] at hs))
    rw [← hurwitzZetaComplex_eq_hurwitzZeta hx0 hx1.le hs1] at h
    have he : exp (-(2 * π * I * (x : ℂ))) = exp (2 * π * I * (-x : ℝ)) := by
      congr 1; push_cast; ring
    rw [he, polylog_exp_eq_expZeta x hs, polylog_exp_eq_expZeta (-x) hs,
      AddCircle.coe_neg]
    rw [h, cpow_neg, show -↑π * I * s / 2 = -(π * I * s / 2) by ring, exp_neg]
    have hphase : exp (π * I * s) = exp (π * I * s / 2) ^ 2 := by
      rw [pow_two, ← exp_add]; congr 1; ring
    rw [hphase]
    have hP : (2 * π : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (by
      exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'))
    field_simp [Gamma_ne_zero_of_re_pos (by linarith : 0 < s.re), hP]
    <;> ring

/-- Differentiating the opposite exponential parameters lowers the polylogarithm order. -/
theorem hasDerivAt_combination (s : ℂ) {w : ℂ} (hw : 0 < w.re ∧ w.re < 1) :
    HasDerivAt (combination s) ((2 * π * I) * combination (s - 1) w) w := by
  have hp := (hasDerivAt_polylog s (exp_mem_slitOne hw) (exp_ne_zero _)).comp w
    (((hasDerivAt_id w).const_mul (2 * π * I)).cexp)
  have hm := (hasDerivAt_polylog s (exp_neg_mem_slitOne hw) (exp_ne_zero _)).comp w
    ((((hasDerivAt_id w).const_mul (2 * π * I)).neg).cexp)
  have he : exp (π * I * (s - 1)) = -exp (π * I * s) := by
    rw [show π * I * (s - 1) = π * I * s - π * I by ring, exp_sub_pi_mul_I]
  convert hp.add (hm.const_mul (exp (π * I * s))) using 1
  · rfl
  · dsimp [combination]
    rw [he]
    field_simp
    <;> ring

/-- The inversion coefficient satisfies the same order-lowering recurrence. -/
theorem coefficient_sub_one (s : ℂ) :
    (2 * π * I) * coefficient (s - 1) = (s - 1) * coefficient s := by
  have hP0 : (2 * π : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'
  have hP := cpow_add (s - 1) 1 hP0
  rw [sub_add_cancel, cpow_one] at hP
  have hE : exp (π * I * s / 2) = I * exp (π * I * (s - 1) / 2) := by
    calc
      _ = exp (π / 2 * I + π * I * (s - 1) / 2) := by congr 1; ring
      _ = _ := by rw [exp_add, exp_pi_div_two_mul_I]
  have hG := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s - 1)
  rw [sub_add_cancel] at hG
  unfold coefficient
  rw [hP, hE]
  simp only [div_eq_mul_inv]
  rw [hG]
  ring

/-- The unit-strip inversion identity descends through any finite number of non-pole
orders. -/
theorem eq_on_strip_of_add_nat {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (N : ℕ)
    (hN : 1 < (s + N).re) {w : ℂ} (hw : 0 < w.re ∧ w.re < 1) :
    combination s w = coefficient s * hurwitzZetaComplex (1 - s) w := by
  induction N generalizing s w with
  | zero => exact eq_on_strip_of_one_lt_re (by simpa using hN) hw
  | succ N ih =>
    have hs0 : s ≠ 0 := by simpa using hs 0
    have hs1 : s + 1 ≠ 0 := by simpa [eq_neg_iff_add_eq_zero] using hs 1
    have hsN : ∀ n : ℕ, s + 1 ≠ -n := by
      intro n h
      apply hs (n + 1)
      push_cast
      linear_combination h
    have hNe : 1 < (s + 1 + N).re := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hN
    have hev : combination (s + 1) =ᶠ[𝓝 w]
        fun v => coefficient (s + 1) * hurwitzZetaComplex (1 - (s + 1)) v := by
      filter_upwards [((isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_re continuous_const)).mem_nhds hw] with v hv
      exact ih hsN hNe hv
    have hleft := hasDerivAt_combination (s + 1) hw
    have hz0 : 1 - (s + 1) ≠ 0 := by simpa using hs0
    have hz1 : 1 - (s + 1) ≠ 1 := by
      intro h; exact hs1 (by linear_combination -h)
    have hright := (hasDerivAt_hurwitzZetaComplex_param' hz0 hz1 hw.1).const_mul
      (coefficient (s + 1))
    have hd := hleft.unique (hright.congr_of_eventuallyEq hev)
    have hc := coefficient_sub_one (s + 1)
    simp only [add_sub_cancel_right] at hd hc
    have harg : 1 - (s + 1) + 1 = 1 - s := by ring
    rw [harg] at hd
    apply mul_left_cancel₀ (show (2 * π * I : ℂ) ≠ 0 by
      exact mul_ne_zero (by exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 2)
        Real.pi_pos).ne') I_ne_zero)
    calc
      _ = coefficient (s + 1) * (-(1 - (s + 1)) *
        hurwitzZetaComplex (1 - s) w) := hd
      _ = _ := by
        rw [show -(1 - (s + 1)) = s by ring]
        linear_combination -hurwitzZetaComplex (1 - s) w * hc

/-- The inversion identity for orders outside the nonpositive integers. -/
theorem eq_on_strip {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) {w : ℂ}
    (hw : 0 < w.re ∧ w.re < 1) :
    combination s w = coefficient s * hurwitzZetaComplex (1 - s) w := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 - s.re)
  exact eq_on_strip_of_add_nat hs N (by simp only [add_re, natCast_re]; linarith) hw

/-- At order zero the opposite exponential parameters sum to `-1`. -/
theorem combination_zero {w : ℂ} (hw : 0 < w.re ∧ w.re < 1) :
    combination 0 w = -1 := by
  have hp := exp_mem_slitOne hw
  have hm := exp_neg_mem_slitOne hw
  have h1 : exp (2 * π * I * w) ≠ 1 := by
    intro h; simpa [h, slitOne] using hp
  unfold combination
  rw [polylog_zero_order hp, polylog_zero_order hm]
  simp only [mul_zero, exp_zero, one_mul, exp_neg]
  field_simp
  <;> simp_all
  <;> ring

/-- The inversion combination vanishes at all negative integer orders. -/
theorem combination_neg_nat (n : ℕ) {w : ℂ} (hw : 0 < w.re ∧ w.re < 1) :
    combination (-n) w = if n = 0 then -1 else 0 := by
  induction n generalizing w with
  | zero => simpa using combination_zero hw
  | succ n ih =>
    have hev : combination (-(n : ℂ)) =ᶠ[𝓝 w] fun _ => if n = 0 then -1 else 0 := by
      filter_upwards [((isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_re continuous_const)).mem_nhds hw] with v hv
      exact ih hv
    have hd := (hasDerivAt_combination (-(n : ℂ)) hw).unique
      ((hasDerivAt_const w (if n = 0 then (-1 : ℂ) else 0)).congr_of_eventuallyEq hev)
    have hn : -(n : ℂ) - 1 = -((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hn] at hd
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    exact (mul_eq_zero.mp hd).resolve_left (mul_ne_zero (by
      exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne') I_ne_zero)

/-- The branch-corrected inversion identity on the unit strip at every nonzero order. -/
theorem eq_on_strip_of_ne_zero {s : ℂ} (hs : s ≠ 0) {w : ℂ}
    (hw : 0 < w.re ∧ w.re < 1) :
    combination s w = coefficient s * hurwitzZetaComplex (1 - s) w := by
  by_cases h : ∃ n : ℕ, s = -n
  · obtain ⟨n, rfl⟩ := h
    have hn : n ≠ 0 := by intro h; simpa [h] using hs
    rw [combination_neg_nat n hw]
    simp [hn, coefficient, Gamma_neg_nat_eq_zero]
  · exact eq_on_strip (by simpa using h) hw

/-- The logarithmic parameter for inversion has real part strictly between zero and one. -/
theorem logarithmicParameter_mem_strip {z : ℂ} (hz : z.im ≠ 0 ∨ z.re < 0) :
    0 < (1 / 2 + Complex.log (-z) / (2 * π * I)).re ∧
      (1 / 2 + Complex.log (-z) / (2 * π * I)).re < 1 := by
  have h0 := neg_pi_lt_arg (-z)
  have h1 : arg (-z) < π := arg_lt_pi_iff.mpr (by
    rcases hz with h | h
    · right; simpa using h
    · left; simpa using (neg_pos.mpr h).le)
  have hr : (1 / 2 + Complex.log (-z) / (2 * π * I)).re =
      1 / 2 + arg (-z) / (2 * π) := by
    simp only [add_re, div_re, one_re, one_im, re_ofNat, im_ofNat, mul_re, mul_im,
      ofReal_re, ofReal_im, I_re, I_im, zero_mul, mul_zero, sub_zero, add_zero,
      zero_add, one_mul, mul_one, log_im, normSq_apply]
    field_simp
    <;> ring
  rw [hr]
  constructor
  · have h : -(1 / 2 : ℝ) < arg (-z) / (2 * π) :=
      (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)).mpr (by linarith)
    linarith
  · have h : arg (-z) / (2 * π) < (1 / 2 : ℝ) :=
      (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * π)).mpr (by linarith)
    linarith

/-- Exponentiating the logarithmic inversion parameter returns the original argument. -/
theorem exp_logarithmicParameter {z : ℂ} (hz : z ≠ 0) :
    exp (2 * π * I * (1 / 2 + Complex.log (-z) / (2 * π * I))) = z := by
  have hP0 : (2 * π * I : ℂ) ≠ 0 := mul_ne_zero (by
    exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne') I_ne_zero
  rw [show 2 * π * I * (1 / 2 + Complex.log (-z) / (2 * π * I)) =
      π * I + Complex.log (-z) by field_simp,
    exp_add, exp_pi_mul_I, exp_log (neg_ne_zero.mpr hz)]
  ring

end PolylogInversion

/-- **Inversion formula** (DLMF 25.12.13, **branch corrected**): for `z ∈ ℂ \ [0, ∞)` and `s ≠ 0`,
`Li_s(z) + e^{πis} Li_s(1/z) = ((2π)^s e^{πis/2}/Γ(s)) ζ(1-s, ln z/(2πi))` with `0 < ph z < 2π`,
i.e. `ln z/(2πi) = 1/2 + ln(-z)/(2πi)`, `ln(-z)` principal. (With principal `ln z` the printed
identity fails for `Im z < 0`; see the module docstring.) -/
@[dlmf 25.12.E13]
theorem polylog_add_exp_mul_polylog_inv {s z : ℂ} (hs : s ≠ 0) (hz : z.im ≠ 0 ∨ z.re < 0) :
    polylog s z + cexp (π * I * s) * polylog s (1 / z) =
      (2 * π) ^ s * cexp (π * I * s / 2) / Gamma s *
        hurwitzZetaComplex (1 - s) (1 / 2 + Complex.log (-z) / (2 * π * I)) := by
  have hz0 : z ≠ 0 := by
    intro h; simpa [h] using hz
  have hw := PolylogInversion.logarithmicParameter_mem_strip hz
  have h := PolylogInversion.eq_on_strip_of_ne_zero hs hw
  have hp := PolylogInversion.exp_logarithmicParameter hz0
  dsimp only [PolylogInversion.combination, PolylogInversion.coefficient] at h
  rw [hp, exp_neg, hp] at h
  simpa only [one_div] using h

end DLMF.Zeta
