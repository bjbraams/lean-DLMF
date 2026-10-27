/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Relations

/-!
# Both Hermite normalizations of cylinder functions

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open Polynomial

/-- Complex form of `H_n(x) = (√2)^n He_n(√2 x)`. -/
theorem aeval_hermitePolyH_eq_hermite_complex (n : ℕ) (x : ℂ) :
    aeval x (DLMF.OrthogonalPolynomials.hermitePolyH n) =
      (Real.sqrt 2 : ℂ) ^ n * aeval ((Real.sqrt 2 : ℂ) * x) (hermite n) := by
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hd := congrArg (fun f : ℂ → ℂ => deriv f x) (funext ih)
    have hcomp : HasDerivAt (fun y : ℂ => (aeval ((Real.sqrt 2 : ℂ) * y) (hermite n) : ℂ))
        (aeval ((Real.sqrt 2 : ℂ) * x) (derivative (hermite n)) * ((Real.sqrt 2 : ℂ) * 1)) x :=
      ((hermite n).hasDerivAt_aeval ((Real.sqrt 2 : ℂ) * x)).comp x
        ((hasDerivAt_id x).const_mul (Real.sqrt 2 : ℂ))
    rw [deriv_const_mul_field, hcomp.deriv, Polynomial.deriv_aeval] at hd
    simp only [mul_one] at hd
    simp only [DLMF.OrthogonalPolynomials.hermitePolyH_succ, hermite_succ, map_sub, map_mul,
      map_ofNat, aeval_X, ih, hd, pow_succ]
    linear_combination (-(Real.sqrt 2:ℂ)^n * x * aeval ((Real.sqrt 2 : ℂ) * x) (hermite n)) * hs

/-- `2^{-n/2} (√2)^n = 1`. -/
theorem two_cpow_neg_half_mul_sqrt_two_pow (n : ℕ) :
    (2:ℂ)^(-(n:ℂ)/2) * (Real.sqrt 2 : ℂ)^n = 1 := by
  rw [← two_cpow_half, ← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ two_ne_zero]
  ring_nf; simp


/-- pcfU physicists hermite. -/
@[dlmf 12.7.E2]
theorem pcfU_physicists_hermite (n : ℕ) (z : ℂ) :
    pcfU (-n-1/2) z=2^(-(n:ℂ)/2)*exp (-z^2/4)*Polynomial.aeval (z/Real.sqrt 2) (DLMF.OrthogonalPolynomials.hermitePolyH n) := by
  have hs0 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have h := pcfD_nat n z
  rw [pcfD] at h
  rw [h, aeval_hermitePolyH_eq_hermite_complex, mul_div_cancel₀ _ hs0]
  linear_combination (-(exp (-z^2/4) * aeval z (hermite n))) * two_cpow_neg_half_mul_sqrt_two_pow n

/-- pcfV physicists hermite. -/
@[dlmf 12.7.E3]
theorem pcfV_physicists_hermite (n : ℕ) (z : ℂ) :
    pcfV (n+1/2) z=(Real.sqrt (2/π):ℂ)*exp (z^2/4)*(-I)^n*2^(-(n:ℂ)/2)*Polynomial.aeval (I*z/Real.sqrt 2) (DLMF.OrthogonalPolynomials.hermitePolyH n) := by
  have hs0 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  rw [pcfV_nat_add_half, aeval_hermitePolyH_eq_hermite_complex, mul_div_cancel₀ _ hs0]
  linear_combination (-((Real.sqrt (2/π):ℂ)*exp (z^2/4)*(-I)^n * aeval (I*z) (hermite n))) *
    two_cpow_neg_half_mul_sqrt_two_pow n

end DLMF.Confluent
