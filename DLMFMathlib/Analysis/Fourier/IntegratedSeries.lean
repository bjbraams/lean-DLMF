/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import DLMFMathlib.Analysis.Fourier.CosineKernelConvergence
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
/-!
# Integration of Fourier series

Absolute continuity and almost-everywhere integration by parts relate the cosine and sine
coefficients of a primitive to those of its derivative. The Fourier-kernel convergence used
below requires only absolute continuity. Integration by parts uses TauCeti's
`AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt`.
-/

public noncomputable section
open Complex Filter Set MeasureTheory
open scoped Real Topology
namespace Real
/-- Integration by parts exchanges sine and cosine moments of an almost-everywhere
derivative when the primitive vanishes at both endpoints. -/
lemma integral_mul_cos_and_sin_of_ae_hasDerivAt {G F : ℝ → ℂ} {a b : ℝ}
    (hG : AbsolutelyContinuousOnInterval G a b)
    (hd : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt G (F t) t)
    (ha : G a = 0) (hb : G b = 0) (ω : ℝ) :
    (∫ t in a..b, F t * (cos (ω * t) : ℂ)) =
      (ω : ℂ) * ∫ t in a..b, G t * (sin (ω * t) : ℂ) ∧
    (∫ t in a..b, F t * (sin (ω * t) : ℂ)) =
      -(ω : ℂ) * ∫ t in a..b, G t * (cos (ω * t) : ℂ) := by
  have hcos : ∀ t, HasDerivAt (fun t : ℝ => (cos (ω * t) : ℂ))
      (-((ω : ℂ) * (sin (ω * t) : ℂ))) t := by
    intro t
    convert ((hasDerivAt_id t).const_mul ω).cos.ofReal_comp using 1 <;>
      simp only [id_eq, mul_one, ofReal_neg, ofReal_mul]
    ring_nf
  have hsin : ∀ t, HasDerivAt (fun t : ℝ => (sin (ω * t) : ℂ))
      ((ω : ℂ) * (cos (ω * t) : ℂ)) t := by
    intro t
    convert ((hasDerivAt_id t).const_mul ω).sin.ofReal_comp using 1 <;>
      simp only [id_eq, mul_one, ofReal_mul]
    ring_nf
  have hcc : AbsolutelyContinuousOnInterval (fun t : ℝ => (cos (ω * t) : ℂ)) a b :=
    (Complex.ofRealCLM.contDiff.comp
      (((contDiff_const (c := ω)).mul contDiff_id).cos)).contDiffOn.absolutelyContinuousOnInterval
  have hsc : AbsolutelyContinuousOnInterval (fun t : ℝ => (sin (ω * t) : ℂ)) a b :=
    (Complex.ofRealCLM.contDiff.comp
      (((contDiff_const (c := ω)).mul contDiff_id).sin)).contDiffOn.absolutelyContinuousOnInterval
  have hc := hcc.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt hG
    (ae_of_all _ fun t _ => hcos t) hd
  have hs := hsc.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt hG
    (ae_of_all _ fun t _ => hsin t) hd
  simp only [ha, hb, mul_zero, sub_self, zero_sub] at hc hs
  constructor
  · calc
      _ = ∫ t in a..b, (cos (ω * t) : ℂ) * F t := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := hc
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro t _
        ring
  · calc
      _ = ∫ t in a..b, (sin (ω * t) : ℂ) * F t := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := hs
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro t _
        ring
/-- Integrating the Fourier series of an integrable function over a subinterval gives the
primitive of the function minus its mean, including at both period endpoints. -/
lemma tendsto_integral_fourierSeries_of_intervalIntegrable {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 (2 * π)) {x : ℝ} (hx : x ∈ Icc 0 (2 * π)) :
    let a : ℕ → ℂ := fun n => (1 / π : ℂ) * ∫ t in (0 : ℝ)..2 * π, f t * (cos (n * t) : ℂ)
    let b : ℕ → ℂ := fun n => (1 / π : ℂ) * ∫ t in (0 : ℝ)..2 * π, f t * (sin (n * t) : ℂ)
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (a (n + 1) * (sin ((n + 1 : ℕ) * x) : ℂ) +
          b (n + 1) * (1 - (cos ((n + 1 : ℕ) * x) : ℂ))) / ((n + 1 : ℕ) : ℂ))
      atTop (𝓝 (∫ t in (0 : ℝ)..x, (f t - a 0 / 2))) := by
  let A : ℕ → ℂ := fun n => (1 / π : ℂ) * ∫ t in (0 : ℝ)..2 * π,
    f t * (cos (n * t) : ℂ)
  let B : ℕ → ℂ := fun n => (1 / π : ℂ) * ∫ t in (0 : ℝ)..2 * π,
    f t * (sin (n * t) : ℂ)
  let c : ℂ := A 0 / 2
  let q : ℝ → ℂ := fun t => f t - c
  let G : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, q s
  have hq : IntervalIntegrable q volume 0 (2 * π) := hf.sub intervalIntegrable_const
  have hG : AbsolutelyContinuousOnInterval G 0 (2 * π) :=
    hq.absolutelyContinuousOnInterval_intervalIntegral' left_mem_uIcc
  have hG0 : G 0 = 0 := by simp [G]
  have hGT : G (2 * π) = 0 := by
    dsimp only [G, q]
    rw [intervalIntegral.integral_sub hf intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [c, A, CharP.cast_eq_zero, zero_mul, cos_zero, ofReal_one, mul_one,
      sub_zero, Complex.real_smul, ofReal_mul, ofReal_ofNat]
    field_simp
    ring_nf
  have hd : ∀ᵐ t, t ∈ uIoc (0 : ℝ) (2 * π) → HasDerivAt G (q t) t := by
    filter_upwards [hq.ae_hasDerivAt_integral] with t ht hmem
    exact ht (uIoc_subset_uIcc hmem) 0 left_mem_uIcc
  let aG : ℕ → ℂ := fun n => (1 / π : ℂ) * ∫ t in (0 : ℝ)..2 * π,
    G t * (cos (n * t) : ℂ)
  let bG : ℕ → ℂ := fun n => (1 / π : ℂ) * ∫ t in (0 : ℝ)..2 * π,
    G t * (sin (n * t) : ℂ)
  have hsinNat (n : ℕ) : sin ((n : ℝ) * (2 * π)) = 0 := by
    simpa only [zero_add, sin_zero] using sin_add_nat_mul_two_pi 0 n
  have htrig (n : ℕ) (hn : 0 < n) :
      (∫ t in (0 : ℝ)..2 * π, (cos (n * t) : ℂ)) = 0 ∧
      (∫ t in (0 : ℝ)..2 * π, (sin (n * t) : ℂ)) = 0 := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    constructor
    · rw [intervalIntegral.integral_ofReal,
        intervalIntegral.integral_comp_mul_left cos hn0, integral_cos]
      simp only [mul_zero, sin_zero, hsinNat, sub_zero, smul_zero, ofReal_zero]
    · rw [intervalIntegral.integral_ofReal,
        intervalIntegral.integral_comp_mul_left sin hn0, integral_sin]
      simp only [mul_zero, cos_zero, cos_nat_mul_two_pi, sub_self, smul_zero, ofReal_zero]
  have hcoeff (n : ℕ) (hn : 0 < n) : A n = n * bG n ∧ B n = -(n * aG n) := by
    have hi := integral_mul_cos_and_sin_of_ae_hasDerivAt hG hd hG0 hGT (n : ℝ)
    have hc (tr : ℝ → ℝ) (htr : Continuous tr)
        (hz : (∫ t in (0 : ℝ)..2 * π, (tr t : ℂ)) = 0) :
        (∫ t in (0 : ℝ)..2 * π, q t * (tr t : ℂ)) =
          ∫ t in (0 : ℝ)..2 * π, f t * (tr t : ℂ) := by
      dsimp only [q]
      simp_rw [sub_mul]
      erw [intervalIntegral.integral_sub
        (hf.mul_continuousOn (Complex.continuous_ofReal.comp htr).continuousOn)
        (((Complex.continuous_ofReal.comp htr).intervalIntegrable _ _).const_mul c),
        intervalIntegral.integral_const_mul, hz, mul_zero, sub_zero]
      rfl
    rw [hc _ (by fun_prop) (htrig n hn).1] at hi
    rw [hc _ (by fun_prop) (htrig n hn).2] at hi
    constructor
    · dsimp only [A, bG]
      rw [hi.1]
      push_cast
      ring_nf
    · dsimp only [B, aG]
      rw [hi.2]
      push_cast
      ring_nf
  have hK (N : ℕ) (y : ℝ) :
      (1 / π : ℂ) * (∫ t in (0 : ℝ)..2 * π,
        G t * (cosinePartialSumKernel N (t - y) : ℂ)) =
        (1 / π : ℂ) * (1 / 2 : ℂ) * (∫ t in (0 : ℝ)..2 * π, G t) +
          ∑ n ∈ Finset.range N,
            (aG (n + 1) * (cos ((n + 1 : ℕ) * y) : ℂ) +
             bG (n + 1) * (sin ((n + 1 : ℕ) * y) : ℂ)) := by
    erw [integral_mul_cosinePartialSumKernel_eq hG.continuousOn.intervalIntegrable y N]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro n _
      dsimp only [aG, bG]
      simp only [RCLike.ofReal, Complex.coe_algebraMap]
      ring_nf
  have hfinite (N : ℕ) :
      (∑ n ∈ Finset.range N,
        (A (n + 1) * (sin ((n + 1 : ℕ) * x) : ℂ) +
          B (n + 1) * (1 - (cos ((n + 1 : ℕ) * x) : ℂ))) / ((n + 1 : ℕ) : ℂ)) =
      (1 / π : ℂ) * (∫ t in (0 : ℝ)..2 * π,
        G t * (cosinePartialSumKernel N (t - x) : ℂ)) -
      (1 / π : ℂ) * (∫ t in (0 : ℝ)..2 * π,
        G t * (cosinePartialSumKernel N t : ℂ)) := by
    have hk0 := hK N 0
    simp only [sub_zero, mul_zero, cos_zero, sin_zero, ofReal_one, ofReal_zero,
      mul_one, mul_zero, add_zero] at hk0
    rw [hK, hk0, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [(hcoeff (n + 1) (by omega)).1, (hcoeff (n + 1) (by omega)).2]
    have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp [hn]
    ring_nf
  have htarget : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      (A (n + 1) * (sin ((n + 1 : ℕ) * x) : ℂ) +
        B (n + 1) * (1 - (cos ((n + 1 : ℕ) * x) : ℂ))) / ((n + 1 : ℕ) : ℂ))
      atTop (𝓝 (G x)) := by
    rcases hx.1.eq_or_lt with h0 | hx0
    · rw [← h0, hG0]
      simpa only [mul_zero, sin_zero, cos_zero, ofReal_zero, ofReal_one, mul_zero,
        sub_self, zero_add, zero_div, Finset.sum_const_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    · rcases hx.2.eq_or_lt with hT | hxT
      · rw [hT, hGT]
        simpa only [hsinNat, cos_nat_mul_two_pi, ofReal_zero, ofReal_one,
          mul_zero, sub_self, zero_add, zero_div, Finset.sum_const_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
      · have hi := tendsto_integral_cosinePartialSumKernel_of_mem_Ioo hG hx0 hxT
        have he := tendsto_integral_cosinePartialSumKernel_zero hG
        simp only [hG0, hGT, add_zero, zero_div] at he
        have h := hi.sub he
        simp only [sub_zero] at h
        simpa only [hfinite] using h
  exact htarget

end Real
