/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The real digamma function

This file defines the real digamma function `ψ(x) = Γ'(x)/Γ(x)` and proves its basic
properties on `(0, ∞)`: the bridge to Mathlib's complex digamma function, the special values
at the positive integers, the recurrence and the reflection formula.

## Main definitions

* `Real.digamma`: the real digamma function `ψ(x) = Γ'(x)/Γ(x)`.

## Main results

* `Real.digamma_eq_deriv_log`, `Real.hasDerivAt_log_Gamma`: `log Γ` has derivative `ψ` on
  `(0, ∞)`.
* `Real.digamma_eq_re_digamma`: agreement with the real part of Mathlib's `Complex.digamma`.
* `Real.digamma_one`, `Real.digamma_nat_add_one`: `ψ(1) = -γ` and `ψ(n+1) = -γ + H_n`
  (DLMF 5.4.12, 5.4.14).
* `Real.digamma_add_one`, `Real.digamma_add_nat`: the recurrence `ψ(x+1) = ψ(x) + 1/x`
  (DLMF 5.5.2).
* `Real.digamma_one_sub`: the reflection formula `ψ(1-x) - ψ(x) = π cot(π x)` on `(0, 1)`.

## Implementation notes

DLMF's `ψ` is complex; Mathlib's `Complex.digamma` covers that case, and this real version is the
one used in the AAR-based parts of the project. The series `ψ(x) = -γ + ∑ (1/(k+1) - 1/(x+k))`
and the trigamma function are in `DLMF.Gamma.Digamma`.
-/

@[expose] public section

open Filter Finset Set

open scoped Topology Real

noncomputable section

namespace Real

local notation "γ" => eulerMascheroniConstant

/-- The real digamma function `ψ(x) = Γ'(x)/Γ(x)`. -/
def digamma (x : ℝ) : ℝ :=
  deriv Gamma x / Gamma x

/-- For `x > 0`, `ψ(x)` is the derivative of `log Γ` at `x`. -/
theorem digamma_eq_deriv_log {x : ℝ} (hx : 0 < x) :
    digamma x = deriv (log ∘ Gamma) x := by
  have hG : DifferentiableAt ℝ Gamma x :=
    differentiableAt_Gamma fun m => ((neg_nonpos.mpr m.cast_nonneg).trans_lt hx).ne'
  rw [digamma, Function.comp_def, deriv.log hG (Gamma_pos_of_pos hx).ne']

open ComplexConjugate in
/-- The real digamma function is the real part of Mathlib's complex digamma function. -/
theorem digamma_eq_re_digamma {x : ℝ} (hx : 0 < x) :
    digamma x = (Complex.digamma x).re := by
  have hx' : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h => by
    have : x = -(m : ℝ) := by exact_mod_cast h
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hd : HasDerivAt Gamma (deriv Complex.Gamma x).re x :=
    (Complex.differentiableAt_Gamma _ hx').hasDerivAt.real_of_complex
  have hconj : conj (deriv Complex.Gamma x) = deriv Complex.Gamma x := by
    have h := congrFun (deriv_conj_conj (f := Complex.Gamma)) (x : ℂ)
    have hfun : (conj ∘ Complex.Gamma ∘ conj) = Complex.Gamma := by
      funext z
      simp [Function.comp_def, Complex.Gamma_conj]
    rw [hfun] at h
    simp only [Function.comp_def, Complex.conj_ofReal] at h
    exact h.symm
  have hre : deriv Complex.Gamma x = ((deriv Complex.Gamma x).re : ℂ) :=
    (Complex.conj_eq_iff_re.mp hconj).symm
  rw [digamma, hd.deriv, Complex.digamma_def, logDeriv_apply, Complex.Gamma_ofReal]
  conv_rhs => rw [hre]
  rw [Complex.div_ofReal_re, Complex.ofReal_re]

/-- DLMF 5.4.12: `ψ(1) = -γ`. -/
@[dlmf 5.4.E12]
theorem digamma_one : digamma 1 = -γ := by
  simp [digamma, hasDerivAt_Gamma_one.deriv]

/-- Recurrence `ψ(x+1) = ψ(x) + 1/x`. -/
@[dlmf 5.5.E2]
theorem digamma_add_one {x : ℝ} (hx : 0 < x) : digamma (x + 1) = digamma x + x⁻¹ := by
  have hx' : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h => by
    have : x = -(m : ℝ) := by exact_mod_cast h
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [digamma_eq_re_digamma (by linarith), digamma_eq_re_digamma hx, Complex.ofReal_add,
    Complex.ofReal_one, Complex.digamma_apply_add_one _ hx', Complex.add_re,
    ← Complex.ofReal_inv, Complex.ofReal_re]

/-- `ψ(x + n) = ψ(x) + ∑_{k<n} 1/(x+k)` for `x > 0`. -/
theorem digamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    digamma (x + n) = digamma x + ∑ k ∈ range n, (x + k)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx' : 0 < x + n := add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg n)
    rw [Nat.cast_succ, ← add_assoc, digamma_add_one hx', ih, sum_range_succ]
    ring

/-- `ψ(n+1) = -γ + H_n`. -/
@[dlmf 5.4.E14]
theorem digamma_nat_add_one (n : ℕ) :
    digamma (n + 1) = -γ + (harmonic n : ℝ) := by
  have := digamma_add_nat (by positivity : (0 : ℝ) < 1) n
  simpa [digamma_one, harmonic, add_comm, add_left_comm] using this

/-- For `x > 0`, `log Γ` has derivative `ψ(x)` at `x`. -/
theorem hasDerivAt_log_Gamma {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => log (Gamma y)) (digamma x) x := by
  have hG : DifferentiableAt ℝ Gamma x :=
    differentiableAt_Gamma fun m =>
      ((neg_nonpos.mpr m.cast_nonneg).trans_lt hx).ne'
  have hlog := hG.hasDerivAt.log (Gamma_pos_of_pos hx).ne'
  simpa [digamma, Function.comp_def] using hlog

/-- Reflection formula for the digamma function, AAR (1.2.18). -/
public theorem digamma_one_sub {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    digamma (1 - x) - digamma x = π * cot (π * x) := by
  have hint : ∀ n : ℤ, (x : ℂ) ≠ n := fun n h => by
    have hxn : x = n := by exact_mod_cast h
    have h1 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
    have h2 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
    omega
  have h := Complex.digamma_one_sub hint
  rw [digamma_eq_re_digamma (by linarith), digamma_eq_re_digamma hx0, Complex.ofReal_sub,
    Complex.ofReal_one, h, Complex.add_re, ← Complex.ofReal_mul, ← Complex.ofReal_cot,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

end Real
