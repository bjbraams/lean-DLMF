/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Associated

/-!
# Shared tools for addition theorems and spherical harmonics

This file contains helper results used by the spherical-harmonic and Legendre addition-theorem
files.

## Main results

* `addTools_conj_regularizedGaussHG`: conjugation symmetry of the regularized Gauss function
  `𝐅(a,b;c;z)` on the whole cut plane, by the identity theorem from the disk case
  `DLMF.Legendre.regularizedGaussHG_conj`.
* `addTools_conj_eval_map_ofReal`, `addTools_iteratedDeriv_even_neg`: real polynomials commute
  with conjugation, and derivatives of even functions have parity `(-1)^k`.
* `addTools_legendreBranchPower_I_mul`: the principal-branch value of the Legendre branch power
  `(z²-1)^{m/2}` on the positive imaginary axis, used for the oblate spheroidal harmonics of
  DLMF §14.30(i).
-/

@[expose] public noncomputable section

open Complex Filter Set DLMF.Hypergeometric DLMF
open scoped Real Topology ComplexConjugate

namespace DLMF.SphericalHarmonics

open DLMF.Legendre

/-- Conjugation symmetry of the regularized Gauss function on the whole cut plane
`ℂ \ [1, ∞)`, extending `DLMF.Legendre.regularizedGaussHG_conj` from the unit disk by the
identity theorem. -/
theorem addTools_conj_regularizedGaussHG (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    conj (regularizedGaussHG a b c z) =
      regularizedGaussHG (conj a) (conj b) (conj c) (conj z) := by
  have hconjCut : ∀ w ∈ cutPlane, conj w ∈ cutPlane := by
    intro w hw
    simp only [cutPlane, mem_ofPred_eq] at hw ⊢
    rw [show 1 - conj w = conj (1 - w) by simp]
    rw [mem_slitPlane_iff] at hw ⊢
    simp only [conj_re, conj_im, neg_ne_zero]; exact hw
  have hg : AnalyticOnNhd ℂ (conj ∘ regularizedGaussHG a b c ∘ conj) cutPlane := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_cutPlane
    have h := (differentiableAt_regularizedGaussHG a b c (hconjCut w hw)).conj_conj
    rw [conj_conj] at h
    exact h.differentiableWithinAt
  have hEq := eqOn_cutPlane_of_eqOn_ball hg
      (analyticOnNhd_regularizedGaussHG (conj a) (conj b) (conj c))
    one_pos (fun w hw => by
      have hw' : ‖conj w‖ < 1 := by rw [RCLike.norm_conj]; simpa using hw
      simp only [Function.comp, regularizedGaussHG_conj hw', conj_conj])
  have := hEq (hconjCut z hz)
  simpa only [Function.comp, conj_conj] using this

/-- A real polynomial commutes with complex conjugation. -/
theorem addTools_conj_eval_map_ofReal (p : Polynomial ℝ) (z : ℂ) :
    conj ((p.map ofRealHom).eval z) = (p.map ofRealHom).eval (conj z) := by
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂]
  congr 1
  ext r; simp

/-- Derivatives of an even function have parity `(-1)^k`. -/
theorem addTools_iteratedDeriv_even_neg {f : ℂ → ℂ} (hf : ∀ z, f (-z) = f z) (k : ℕ) (z : ℂ) :
    iteratedDeriv k f (-z) = (-1)^k * iteratedDeriv k f z := by
  have h := iteratedDeriv_comp_neg k f z
  have hf' : (fun x => f (-x)) = f := funext hf
  rw [hf', smul_eq_mul] at h
  rw [h, ← mul_assoc, ← mul_pow]; norm_num

/-- `log(ix - 1) + log(ix + 1) = log(1 + x²) + πi` for `x > 0` (principal branches). -/
theorem addTools_log_I_mul (x : ℝ) (hx : 0 < x) :
    log (I*x - 1) + log (I*x + 1) = Real.log (1 + x^2) + π * I := by
  have hn : ‖(I*x+1 : ℂ)‖ = Real.sqrt (1 + x^2) := by
    rw [show (I*x+1 : ℂ) = ⟨1, x⟩ by apply Complex.ext <;> simp, Complex.norm_def,
                                       Complex.normSq_mk]
    congr 1; ring
  have hn' : ‖(I*x-1 : ℂ)‖ = Real.sqrt (1 + x^2) := by
    rw [show (I*x-1 : ℂ) = ⟨-1, x⟩ by apply Complex.ext <;> simp, Complex.norm_def,
                                        Complex.normSq_mk]
    congr 1; ring
  have hw : (I*x - 1 : ℂ) = -conj (I*x+1) := by simp; ring
  have him : (conj (I*x+1 : ℂ)).im < 0 := by simp [hx]
  have hpi : arg (I*x+1 : ℂ) ≠ π := by
    intro h; have := (arg_eq_pi_iff).mp h; simp at this; linarith [this.2]
  have harg : arg (I*x - 1 : ℂ) + arg (I*x+1) = π := by
    rw [hw, arg_neg_eq_arg_add_pi_of_im_neg him, arg_conj]; simp only [hpi, ↓reduceIte]; ring
  apply Complex.ext
  · simp only [add_re, log_re, hn, hn', ofReal_re, mul_re, ofReal_im, I_re, I_im]
    rw [← Real.log_mul (by positivity) (by positivity), Real.mul_self_sqrt (by positivity)]
    ring
  · simp only [add_im, log_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, harg]
    ring

/-- The Legendre branch power `(z²-1)^{m/2}` at `z = ix`, `x > 0`, equals `(1+x²)^{m/2} iᵐ`. -/
theorem addTools_legendreBranchPower_I_mul (m : ℕ) (x : ℝ) (hx : 0 < x) :
    legendreBranchPower m (I*x) = (Real.exp (m/2 * Real.log (1+x^2)) : ℂ) * I^m := by
  rw [legendreBranchPower, addTools_log_I_mul x hx,
    show (m:ℂ)/2 * ((Real.log (1+x^2):ℂ) + π*I) =
        ((m/2 * Real.log (1+x^2) : ℝ) : ℂ) + m * (π/2*I) by
      push_cast; ring,
    exp_add, exp_nat_mul, exp_pi_div_two_mul_I, ofReal_exp]

end DLMF.SphericalHarmonics
