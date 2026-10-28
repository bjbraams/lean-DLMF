/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import DLMFMathlib.NumberTheory.EulerPolynomials
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Bernoulli and Euler polynomials: definitions (DLMF §§24.1–24.2)

DLMF's Bernoulli numbers `Bₙ`, Bernoulli polynomials `Bₙ(x)`, Euler numbers `Eₙ` and Euler
polynomials `Eₙ(x)` (§24.2) are, in this project,

* `bernoulli n : ℚ` (Mathlib; DLMF's convention `B₁ = -1/2`, not Mathlib's `bernoulli'`),
* `Polynomial.bernoulli n : ℚ[X]` (Mathlib, DLMF 24.2.5),
* `eulerNumber n : ℚ` (`DLMFMathlib.NumberTheory.EulerPolynomials`, `Eₙ = 2ⁿ Eₙ(1/2)`, DLMF 24.2.9),
* `Polynomial.euler n : ℚ[X]` (`DLMFMathlib.NumberTheory.EulerPolynomials`, the Appell sequence of
  the generating function 24.2.8).

Their real-variable forms are Mathlib's `bernoulliFun n : ℝ → ℝ` and the project's
`eulerFun n : ℝ → ℝ`. No second definition is made here. This file adds

* `bernoulliPolyB n x`, `eulerPolyE n x`: complex evaluation `x ↦ Bₙ(x)`, `x ↦ Eₙ(x)` (DLMF
  §24.1: "`x` real or complex"), via `Polynomial.aeval`, with bridges to the real, rational and
  polynomial forms;
* `periodicBernoulliB n x`, `periodicEulerE n x`: the periodic functions `B̃ₙ(x)`, `Ẽₙ(x)` of
  §24.2(iii) (DLMF 24.2.11–24.2.12), with a bridge to Mathlib's `periodizedBernoulli`;
* the Appell (binomial) property `b24a_appell_aeval` used for 24.2.5, 24.2.10, 24.4.12–13.

Helper declarations of this area carry the prefix `b24a_`.
-/

@[expose] public section

noncomputable section

open Polynomial Finset
open scoped Nat

namespace DLMF.BernoulliEuler

/-! ### Complex evaluation -/

/-- The Bernoulli polynomial `Bₙ(x)` of DLMF §24.2(i) at a complex argument `x`: the complex
evaluation of Mathlib's `Polynomial.bernoulli n` (DLMF 24.2.3, 24.2.5). -/
@[dlmf 24.2.i]
def bernoulliPolyB (n : ℕ) (x : ℂ) : ℂ := aeval x (Polynomial.bernoulli n)

/-- The Euler polynomial `Eₙ(x)` of DLMF §24.2(ii) at a complex argument `x`: the complex
evaluation of the project's `Polynomial.euler n` (DLMF 24.2.8). -/
@[dlmf 24.2.ii]
def eulerPolyE (n : ℕ) (x : ℂ) : ℂ := aeval x (Polynomial.euler n)

/-- Complex evaluation of a rational polynomial at a real point is the real evaluation. -/
theorem b24a_aeval_ofReal (p : ℚ[X]) (x : ℝ) :
    aeval (x : ℂ) p = ((p.map (algebraMap ℚ ℝ)).eval x : ℝ) := by
  have h := Polynomial.aeval_algebraMap_apply (R := ℚ) (A := ℝ) (B := ℂ) x p
  rw [show (algebraMap ℝ ℂ) x = (x : ℂ) from rfl] at h
  rw [h, aeval_def, eval₂_eq_eval_map]; rfl

/-- Complex evaluation of a rational polynomial at a rational point. -/
lemma b24a_aeval_ratCast (p : ℚ[X]) (x : ℚ) : aeval (x : ℂ) p = ((p.eval x : ℚ) : ℂ) := by
  have h := Polynomial.aeval_algebraMap_apply (R := ℚ) (A := ℚ) (B := ℂ) x p
  rw [show (algebraMap ℚ ℂ) x = (x : ℂ) from rfl] at h
  rw [h, Polynomial.coe_aeval_eq_eval]; rfl

/-- Real points: `bernoulliPolyB n x = bernoulliFun n x`. -/
theorem bernoulliPolyB_ofReal (n : ℕ) (x : ℝ) :
    bernoulliPolyB n x = (bernoulliFun n x : ℂ) := b24a_aeval_ofReal _ x

/-- Real points: `eulerPolyE n x = eulerFun n x`. -/
theorem eulerPolyE_ofReal (n : ℕ) (x : ℝ) :
    eulerPolyE n x = (eulerFun n x : ℂ) := b24a_aeval_ofReal _ x

/-- Rational points: `bernoulliPolyB n x = (Polynomial.bernoulli n).eval x`. -/
theorem bernoulliPolyB_ratCast (n : ℕ) (x : ℚ) :
    bernoulliPolyB n x = (((Polynomial.bernoulli n).eval x : ℚ) : ℂ) := b24a_aeval_ratCast _ x

/-- Rational points: `eulerPolyE n x = (Polynomial.euler n).eval x`. -/
theorem eulerPolyE_ratCast (n : ℕ) (x : ℚ) :
    eulerPolyE n x = (((Polynomial.euler n).eval x : ℚ) : ℂ) := b24a_aeval_ratCast _ x

/-- `Bₙ(0) = Bₙ` for the complex wrapper. -/
@[simp]
theorem bernoulliPolyB_zero_arg (n : ℕ) : bernoulliPolyB n 0 = (bernoulli n : ℂ) := by
  have := bernoulliPolyB_ratCast n 0
  simpa using this

/-- `Eₙ(1/2) = 2⁻ⁿ Eₙ` for the complex wrapper. -/
theorem eulerPolyE_half (n : ℕ) : eulerPolyE n (1 / 2) = (eulerNumber n : ℂ) / 2 ^ n := by
  have h := eulerPolyE_ratCast n (1 / 2)
  push_cast at h
  rw [h, eulerNumber]
  push_cast
  field_simp

/-- Identity under the stated parameter and domain assumptions: `bernoulliPolyB 0 x = 1`. -/
@[simp]
theorem bernoulliPolyB_zero (x : ℂ) : bernoulliPolyB 0 x = 1 := by simp [bernoulliPolyB]

/-- Identity under the stated parameter and domain assumptions: `eulerPolyE 0 x = 1`. -/
@[simp]
theorem eulerPolyE_zero (x : ℂ) : eulerPolyE 0 x = 1 := by simp [eulerPolyE]

/-- The Euler numbers are rational numbers `eulerNumber n = 2ⁿ Eₙ(1/2)` (DLMF 24.2.9). -/
theorem eulerNumber_def' (n : ℕ) :
    eulerNumber n = 2 ^ n * (Polynomial.euler n).eval (1 / 2) := rfl

/-! ### The Appell property -/

/-- Iterated derivatives of an Appell sequence `Pₙ' = n Pₙ₋₁`. -/
lemma b24a_iterate_derivative (P : ℕ → ℚ[X])
    (hP : ∀ n, derivative (P (n + 1)) = ((n : ℚ[X]) + 1) * P n) (k m : ℕ) :
    derivative^[k] (P (m + k)) = ((m + k).descFactorial k : ℚ[X]) * P m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, show m + (k + 1) = (m + k) + 1 by ring, hP,
      show ((m + k : ℕ) : ℚ[X]) + 1 = ((m + k + 1 : ℕ) : ℚ[X]) by push_cast; ring,
      iterate_derivative_natCast_mul, ih, Nat.succ_descFactorial_succ]
    push_cast; ring

/-- Hasse derivatives of an Appell sequence. -/
lemma b24a_hasseDeriv (P : ℕ → ℚ[X])
    (hP : ∀ n, derivative (P (n + 1)) = ((n : ℚ[X]) + 1) * P n) (k m : ℕ) :
    hasseDeriv k (P (m + k)) = ((m + k).choose k : ℚ[X]) * P m := by
  have h := congrFun (factorial_smul_hasseDeriv (R := ℚ) (k := k)) (P (m + k))
  rw [b24a_iterate_derivative P hP, Nat.descFactorial_eq_factorial_mul_choose] at h
  simp only [LinearMap.smul_apply] at h
  have hk : (k ! : ℚ) ≠ 0 := by positivity
  apply smul_right_injective ℚ[X] hk
  simp only
  rw [Nat.cast_smul_eq_nsmul ℚ, h, Nat.cast_smul_eq_nsmul ℚ, nsmul_eq_mul]
  push_cast; ring

/-- High Hasse derivatives of an Appell sequence vanish. -/
lemma b24a_hasseDeriv_eq_zero (P : ℕ → ℚ[X]) (h0 : P 0 = 1)
    (hP : ∀ n, derivative (P (n + 1)) = ((n : ℚ[X]) + 1) * P n) {k n : ℕ} (hk : n < k) :
    hasseDeriv k (P n) = 0 := by
  have h := congrFun (factorial_smul_hasseDeriv (R := ℚ) (k := k)) (P n)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  have : derivative^[n + j + 1] (P n) = 0 := by
    rw [show n + j + 1 = (j + 1) + n by ring, Function.iterate_add_apply,
      show P n = P (0 + n) by simp, b24a_iterate_derivative P hP, h0]
    simp [Function.iterate_succ_apply]
  rw [this] at h
  simp only [LinearMap.smul_apply] at h
  have hk : ((n + j + 1)! : ℚ) ≠ 0 := by positivity
  rw [← Nat.cast_smul_eq_nsmul ℚ] at h
  exact (smul_eq_zero.mp h).resolve_left hk

/-- The Appell (binomial) property `Pₙ(x+h) = ∑ₖ (n choose k) Pₖ(x) h^{n-k}` at complex points. -/
lemma b24a_appell_aeval (P : ℕ → ℚ[X]) (h0 : P 0 = 1)
    (hP : ∀ n, derivative (P (n + 1)) = ((n : ℚ[X]) + 1) * P n) (n : ℕ) (x h : ℂ) :
    aeval (x + h) (P n) =
      ∑ k ∈ range (n + 1), (n.choose k : ℂ) * aeval x (P k) * h ^ (n - k) := by
  set Q := (P n).map (algebraMap ℚ ℂ)
  have hdeg : Q.natDegree < n + 1 := by
    rw [Nat.lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
    intro i hi
    have hi' : n < i := by exact_mod_cast hi
    have := congrArg (fun p => p.coeff 0) (b24a_hasseDeriv_eq_zero P h0 hP hi')
    simp only [hasseDeriv_coeff, zero_add, Nat.choose_self, Nat.cast_one, one_mul,
      coeff_zero] at this
    simp [Q, coeff_map, this]
  rw [aeval_def, eval₂_eq_eval_map, add_comm, ← taylor_eval,
    eval_eq_sum_range' (by rwa [natDegree_taylor])]
  rw [← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [taylor_coeff, hasseDeriv_map]
  simp only [show n + 1 - 1 - k = n - k by omega]
  rw [show P n = P (k + (n - k)) by rw [Nat.add_sub_cancel' hk'], b24a_hasseDeriv P hP,
    Nat.add_sub_cancel' hk', Nat.choose_symm hk', aeval_def, eval₂_eq_eval_map]
  simp [Polynomial.map_mul]

/-- The Bernoulli polynomials satisfy `Bₙ₊₁' = (n+1) Bₙ`. -/
lemma b24a_derivative_bernoulli (n : ℕ) :
    derivative (Polynomial.bernoulli (n + 1)) = ((n : ℚ[X]) + 1) * Polynomial.bernoulli n := by
  rw [Polynomial.derivative_bernoulli_add_one]

/-- The Euler polynomials satisfy `Eₙ₊₁' = (n+1) Eₙ`. -/
lemma b24a_derivative_euler (n : ℕ) :
    derivative (Polynomial.euler (n + 1)) = ((n : ℚ[X]) + 1) * Polynomial.euler n :=
  Polynomial.derivative_euler_succ n

/-- **DLMF 24.4.12**: Appell property of the complex Bernoulli polynomials. -/
@[dlmf 24.4.E12]
theorem bernoulliPolyB_add (n : ℕ) (x h : ℂ) :
    bernoulliPolyB n (x + h) =
      ∑ k ∈ range (n + 1), (n.choose k : ℂ) * bernoulliPolyB k x * h ^ (n - k) :=
  b24a_appell_aeval _ Polynomial.bernoulli_zero b24a_derivative_bernoulli n x h

/-- **DLMF 24.4.13**: Appell property of the complex Euler polynomials. -/
@[dlmf 24.4.E13]
theorem eulerPolyE_add (n : ℕ) (x h : ℂ) :
    eulerPolyE n (x + h) =
      ∑ k ∈ range (n + 1), (n.choose k : ℂ) * eulerPolyE k x * h ^ (n - k) :=
  b24a_appell_aeval _ Polynomial.euler_zero b24a_derivative_euler n x h

/-- **Derivative of the Bernoulli polynomials** (DLMF 24.4.34), complex `x`, `n ≥ 1`:
`d/dx Bₙ(x) = n Bₙ₋₁(x)`, written for `n + 1`. -/
@[dlmf 24.4.E34]
theorem hasDerivAt_bernoulliPolyB (n : ℕ) (x : ℂ) :
    HasDerivAt (bernoulliPolyB (n + 1)) (((n : ℂ) + 1) * bernoulliPolyB n x) x := by
  have h := Polynomial.hasDerivAt_aeval (Polynomial.bernoulli (n + 1)) x
  rw [b24a_derivative_bernoulli] at h
  simp only [map_mul, map_add, map_natCast, map_one] at h
  exact h

/-- **Derivative of the Euler polynomials** (DLMF 24.4.35), complex `x`, `n ≥ 1`:
`d/dx Eₙ(x) = n Eₙ₋₁(x)`, written for `n + 1`. -/
@[dlmf 24.4.E35]
theorem hasDerivAt_eulerPolyE (n : ℕ) (x : ℂ) :
    HasDerivAt (eulerPolyE (n + 1)) (((n : ℂ) + 1) * eulerPolyE n x) x := by
  have h := Polynomial.hasDerivAt_aeval (Polynomial.euler (n + 1)) x
  rw [b24a_derivative_euler] at h
  simp only [map_mul, map_add, map_natCast, map_one] at h
  exact h

/-- `Bₙ` is entire. -/
theorem differentiable_bernoulliPolyB (n : ℕ) : Differentiable ℂ (bernoulliPolyB n) :=
  fun x => (Polynomial.hasDerivAt_aeval (Polynomial.bernoulli n) x).differentiableAt

/-- `Eₙ` is entire. -/
theorem differentiable_eulerPolyE (n : ℕ) : Differentiable ℂ (eulerPolyE n) :=
  fun x => (Polynomial.hasDerivAt_aeval (Polynomial.euler n) x).differentiableAt

/-! ### Periodic Bernoulli and Euler functions (DLMF §24.2(iii)) -/

/-- The periodic Bernoulli function `B̃ₙ(x) = Bₙ(x - ⌊x⌋)` of DLMF 24.2.11–24.2.12, real `x`. -/
@[dlmf 24.2.iii]
def periodicBernoulliB (n : ℕ) (x : ℝ) : ℝ := bernoulliFun n (Int.fract x)

/-- The periodic Euler function `Ẽₙ(x) = (-1)^⌊x⌋ Eₙ(x - ⌊x⌋)` of DLMF 24.2.11–24.2.12, real `x`:
the antiperiodic extension of `Eₙ` from `[0, 1)`. -/
@[dlmf 24.2.iii]
def periodicEulerE (n : ℕ) (x : ℝ) : ℝ := (-1 : ℝ) ^ ⌊x⌋ * eulerFun n (Int.fract x)

/-- Bridge to Mathlib's `periodizedBernoulli` on the unit additive circle. -/
theorem periodicBernoulliB_eq_periodizedBernoulli (n : ℕ) (x : ℝ) :
    periodicBernoulliB n x = periodizedBernoulli n (x : UnitAddCircle) := by
  rw [← AddCircle.coe_fract, periodizedBernoulli, AddCircle.liftIco_coe_apply]
  · rfl
  · exact ⟨Int.fract_nonneg x, by simpa using Int.fract_lt_one x⟩

end DLMF.BernoulliEuler
