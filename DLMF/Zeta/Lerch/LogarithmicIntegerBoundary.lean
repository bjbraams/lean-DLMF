/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Zeta.Lerch.LogarithmicContinuation
public import DLMFMathlib.Analysis.SpecialFunctions.Log.Ray

/-!
# Boundary values for the integer logarithmic Lerch formula

Subtracting the logarithmic digamma term gives an expression whose derivative lowers
the positive integer order. At orders at least two, its limit along negative logarithmic
arguments is the Hurwitz zeta value. The logarithmic term tends to zero and the defining
Lerch series converges to its absolutely convergent value on the unit circle.
-/

@[expose] public noncomputable section
open Complex Set Filter MeasureTheory
open scoped Real Topology Nat

namespace DLMF.Zeta.LerchLogarithmic

/-- The weighted Lerch function with its positive-integer logarithmic term removed. -/
def integerExpression (a : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  exp (a * w) * lerchPhi (exp w) (n + 1) a -
    w ^ n / n ! * (digamma (n + 1) - digamma a - log (-w))

/-- The logarithmic correction makes differentiation lower the positive integer order. -/
theorem hasDerivAt_integerExpression_succ {a w : ℂ} (ha : ∀ k : ℕ, a + k ≠ 0)
    (hw : |w.im| < 2 * π) (hw' : -w ∈ slitPlane) (n : ℕ) :
    HasDerivAt (integerExpression a (n + 1)) (integerExpression a n w) w := by
  have hw0 : w ≠ 0 := by intro h; simpa [h] using slitPlane_ne_zero hw'
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hd : digamma ((n : ℂ) + 2) = digamma ((n : ℂ) + 1) + ((n : ℂ) + 1)⁻¹ := by
    have hN : ∀ k : ℕ, (n : ℂ) + 1 ≠ -(k : ℂ) := by
      intro k h
      have hh := congrArg re h
      simp only [add_re, natCast_re, one_re, neg_re] at hh
      linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) k]
    simpa only [show ((n : ℂ) + 1) + 1 = n + 2 by ring] using
      digamma_apply_add_one ((n : ℂ) + 1) hN
  have hlog := (hasDerivAt_id w).neg.clog hw'
  have hpow := (hasDerivAt_pow (n + 1) w).div_const (((n + 1) ! : ℕ) : ℂ)
  have hL := hasDerivAt_exp_mul_lerchPhi ha ((n : ℂ) + 2) (exp_mem_slitOne hw hw')
  have h := hL.sub (hpow.mul ((hlog.const_sub
    (digamma ((n : ℂ) + 2) - digamma a))))
  convert h using 1
  · funext v
    simp only [integerExpression, Nat.cast_add, Nat.cast_one, Pi.sub_apply, Pi.mul_apply,
      Pi.neg_apply, id_eq, show (n : ℂ) + 1 + 1 = n + 2 by ring]
  · simp only [integerExpression, Nat.cast_add, Nat.cast_one, Pi.neg_apply, id_eq,
      Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul] at *
    rw [show (n : ℂ) + 2 - 1 = n + 1 by ring, hd]
    field_simp [hw0, hn, hf]
    ring

/-- At integer orders at least two the logarithmic regularization tends to Hurwitz zeta. -/
theorem tendsto_integerExpression_succ_zero {a : ℂ} (ha : 0 < a.re) (n : ℕ) :
    Tendsto (fun r : ℝ => integerExpression a (n + 1) r) (𝓝[<] 0)
      (𝓝 (hurwitzZetaComplex ((n : ℂ) + 2) a)) := by
  have hr : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[<] 0) (𝓝 0) :=
    (continuous_ofReal.continuousAt.tendsto (x := (0 : ℝ))).mono_left nhdsWithin_le_nhds
  have he := continuous_exp.continuousAt.tendsto.comp (hr.const_mul a)
  simp only [mul_zero, exp_zero] at he
  have hPhi := tendsto_lerchPhi_exp_zero ha (s := (n : ℂ) + 2) (by
    norm_num
    linarith [Nat.cast_nonneg (α := ℝ) n])
  have hZ : lerchPhi 1 ((n : ℂ) + 2) a = hurwitzZetaComplex ((n : ℂ) + 2) a := by
    have hs : 1 < (((n : ℂ) + 2).re) := by
      norm_num
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hPhiSum := hasSum_lerchPhi_of_norm_eq_one' (z := 1) (a := a) hs (by norm_num)
    have ha' : ∀ k : ℕ, a ≠ -(k : ℂ) := by
      intro k hk
      have hh := congrArg re hk
      simp only [neg_re, natCast_re] at hh
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hZSum := hasSum_hurwitzZetaComplex hs ha'
    apply hPhiSum.unique
    simpa only [one_pow, add_comm] using hZSum
  rw [hZ] at hPhi
  have hL := Complex.tendsto_ofReal_pow_div_mul_sub_log_neg_nhdsLT_zero (Nat.succ_pos n)
    (digamma ((n : ℂ) + 2) - digamma a) (((n + 1)! : ℕ) : ℂ)
  have h := (he.mul hPhi).sub hL
  simpa only [integerExpression, Nat.cast_add, Nat.cast_one,
    show (n : ℂ) + 1 + 1 = n + 2 by ring, Function.comp_apply,
    one_mul, sub_zero] using h

end DLMF.Zeta.LerchLogarithmic
