/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMF.Hypergeometric.Basic.Pochhammer
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Carlson.TwoVariable.ThreeFTwoExercises
import DLMF.Hypergeometric.EulerIntegral

/-!
# Endpoint beta integrals of the Gauss hypergeometric function

A beta weight whose first parameter equals the Gauss lower parameter cancels one
numerator and denominator of the resulting `₃F₂`. Gauss summation then evaluates the
integral at unit argument. This includes complex parameters with positive beta endpoints
and positive Gauss excess.

The proof uses the endpoint integration theorem
`Carlson.TwoVariable.betaIntegral_mul_threeFTwo` from `lean-codes` and the project's
`gauss_summation`.

* `threeFTwo_self_lower_eq_ordinaryHypergeometric`: cancellation in the totalized series.
* `integral_cpow_mul_ordinaryHypergeometric`: the endpoint beta integral.
-/

public noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
namespace DLMF.Hypergeometric
/-- Cancelling a regular common parameter of `₃F₂` gives Mathlib's Gauss series. -/
lemma threeFTwo_self_lower_eq_ordinaryHypergeometric (a b c e z : ℂ) (hc : ∀ k : ℕ, c ≠ -k) :
    Carlson.TwoVariable.threeFTwo a b c c e z = ordinaryHypergeometric a b e z := by
  rw [Carlson.TwoVariable.threeFTwo, ordinaryHypergeometric_eq_tsum]
  apply tsum_congr
  intro n
  have hcn : (ascPochhammer ℂ n).eval c ≠ 0 :=
    pochhammer_ne_zero_of_not_neg_nat hc n
  simp only [Carlson.TwoVariable.threeFTwoCoeff, smul_eq_mul]
  field_simp [hcn]
/-- Integrating the Gauss function against its lower-parameter beta weight evaluates by
Gauss summation. Both beta endpoints and the resulting Gauss excess have positive real part. -/
lemma integral_cpow_mul_ordinaryHypergeometric {a b c σ : ℂ}
    (hc : 0 < c.re) (hσ : 0 < σ.re) (hs : 0 < (σ + c - a - b).re) :
    (∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ (c - 1) * (1 - (u : ℂ)) ^ (σ - 1) *
      ordinaryHypergeometric a b c (u : ℂ)) =
      Gamma c * Gamma σ * Gamma (σ + c - a - b) /
        (Gamma (σ + c - a) * Gamma (σ + c - b)) := by
  have hreg : ∀ k : ℕ, c ≠ -k := by
    intro k he
    have := congrArg Complex.re he
    simp only [neg_re, natCast_re] at this
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have h := Carlson.TwoVariable.betaIntegral_mul_threeFTwo (a := a) (b := b)
    (c := c) (d := c) (e := σ + c) (x := 1) hreg hc
    (by simpa using hσ) (by convert hs using 1; ring_nf) (by simp)
  rw [threeFTwo_self_lower_eq_ordinaryHypergeometric a b c (σ + c) 1 hreg] at h
  simp only [add_sub_cancel_right, mul_one] at h
  rw [← h, gauss_summation (c := σ+c) (fun k he => by
    have := congrArg Complex.re he
    simp only [add_re, neg_re, natCast_re] at this
    linarith [Nat.cast_nonneg (α := ℝ) k]) hs,
    betaIntegral_eq_Gamma_mul_div _ _ hc hσ]
  rw [show c + σ = σ + c by ring]
  field_simp [Gamma_ne_zero_of_re_pos (show 0 < (σ + c).re by simp; linarith)]
end DLMF.Hypergeometric
