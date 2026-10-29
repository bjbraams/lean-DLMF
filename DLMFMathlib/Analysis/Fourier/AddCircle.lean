/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Parseval pairings for Fourier series

Mathlib's `HilbertBasis.hasSum_inner_mul_inner` gives the complex Parseval pairing.
The interval version transports this identity through `AddCircle.liftIoc`, as in
Mathlib's `hasSum_sq_fourierCoeffOn`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex AddCircle
open scoped ComplexConjugate

/-- The products of the Fourier coefficients of two square-integrable functions on
the circle sum to their integral pairing, with normalized Haar measure. -/
theorem hasSum_fourierCoeff_mul_conj {T : ℝ} [Fact (0 < T)]
    (f g : Lp ℂ 2 (haarAddCircle (T := T))) :
    HasSum (fun n : ℤ => fourierCoeff f n * conj (fourierCoeff g n))
      (∫ x : AddCircle T, f x * conj (g x) ∂haarAddCircle) := by
  have hc (u : Lp ℂ 2 (haarAddCircle (T := T))) (n : ℤ) :
      inner ℂ (fourierBasis n) u = fourierCoeff u n := by
    rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr]
  convert fourierBasis.hasSum_inner_mul_inner g f using 1
  · ext n
    rw [← inner_conj_symm g (fourierBasis n), hc, hc, mul_comm]
  · simp only [L2.inner_def, RCLike.inner_apply]

/-- Parseval's pairing on an interval: the products of the Fourier coefficients
sum to the integral pairing divided by the interval length. -/
theorem hasSum_fourierCoeffOn_mul_conj {a b : ℝ} {f g : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Ioc a b))) :
    HasSum (fun n : ℤ => fourierCoeffOn hab f n * conj (fourierCoeffOn hab g n))
      ((b - a)⁻¹ • ∫ x in a..b, f x * conj (g x)) := by
  have := Fact.mk (by linarith : 0 < b - a)
  rw [← add_sub_cancel a b] at hf hg
  have hf' := hf.memLp_liftIoc.haarAddCircle
  have hg' := hg.memLp_liftIoc.haarAddCircle
  convert hasSum_fourierCoeff_mul_conj hf'.toLp hg'.toLp using 1
  · simp [fourierCoeff_congr_ae hf'.coeFn_toLp,
      fourierCoeff_congr_ae hg'.coeFn_toLp, fourierCoeff_liftIoc_eq]
  · nth_rw 2 [← add_sub_cancel a b]
    rw [← AddCircle.integral_liftIoc_eq_intervalIntegral,
      ← AddCircle.integral_haarAddCircle]
    apply integral_congr_ae
    filter_upwards [hf'.coeFn_toLp, hg'.coeFn_toLp] with x hx hy
    change AddCircle.liftIoc (b - a) a (fun x => f x * conj (g x)) x =
      (hf'.toLp : AddCircle (b - a) → ℂ) x *
        conj ((hg'.toLp : AddCircle (b - a) → ℂ) x)
    rw [hx, hy]
    rfl
