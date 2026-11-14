/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic
public import DLMF.OrthogonalPolynomials.Basic.AskeyScheme
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import DLMF.BernoulliEuler.Integrals
import DLMF.OrthogonalPolynomials.Hahn.HahnAndMeixner
import DLMFMathlib.Analysis.Integral.HyperbolicCosineMoments
import DLMFMathlib.LinearAlgebra.Matrix.PolynomialMoments
import Mathlib.Algebra.Polynomial.Basis

/-!
# The Euler number Hankel determinant

The moments of the hyperbolic secant measure are the Euler numbers after the variable
change `x ↦ 2ix`. Its monic orthogonal polynomials are rescaled Meixner–Pollaczek
polynomials at `λ = 1 / 2`, `φ = π / 2`, with squared norms `(-1)ⁿ(n!)²`.
The product of squared norms formula gives DLMF 24.14.12.

* `EulerMomentPolynomials.polynomial`: the monic recurrence for the Euler moments.
* `EulerMomentPolynomials.eval_polynomial_two_mul_I`: the Meixner–Pollaczek bridge.
* `eulerNumber_eq_integral_moment`: the complex moments of the hyperbolic secant.
* `det_hankel_eulerNumber`: the Euler number Hankel determinant.

The proof uses Mathlib's polynomial monomial basis and determinant APIs, the project's
proved Meixner–Pollaczek orthogonality and Euler number secant integral, and the generic
polynomial moment determinant factorization.
-/

public noncomputable section

open Polynomial Finset MeasureTheory Complex
open scoped Nat

namespace DLMF.BernoulliEuler.EulerMomentPolynomials

/-- The monic polynomial sequence `P₀ = 1`, `P₁ = X`, `Pₙ₊₂ = X Pₙ₊₁ + (n + 1)² Pₙ`
associated with the Euler number moments. -/
@[expose] def polynomial (R : Type*) [CommRing R] : ℕ → R[X]
  | 0 => 1
  | 1 => X
  | n + 2 => X * polynomial R (n + 1) + C ((n + 1 : R) ^ 2) * polynomial R n

/-- The zeroth Euler moment polynomial is one. -/
@[simp] lemma polynomial_zero (R : Type*) [CommRing R] : polynomial R 0 = 1 := rfl

/-- The first Euler moment polynomial is its variable. -/
@[simp] lemma polynomial_one (R : Type*) [CommRing R] : polynomial R 1 = X := rfl

/-- The three-term recurrence of the monic Euler moment polynomials. -/
lemma polynomial_add_two (R : Type*) [CommRing R] (n : ℕ) : polynomial R (n + 2) =
    X * polynomial R (n + 1) + C ((n + 1 : R) ^ 2) * polynomial R n := rfl

/-- The Euler moment polynomial of index `n` is monic of degree `n`. -/
lemma monic_polynomial_and_natDegree (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) :
    (polynomial R n).Monic ∧ (polynomial R n).natDegree = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn hn1 =>
    rw [polynomial_add_two]
    have hl : (X * polynomial R (n + 1)).Monic := monic_X.mul hn1.1
    have hld : (X * polynomial R (n + 1)).natDegree = n + 2 := by
      rw [natDegree_X_mul hn1.1.ne_zero, hn1.2]
    have hrd : (C ((n + 1 : R) ^ 2) * polynomial R n).natDegree ≤ n :=
      (natDegree_C_mul_le _ _).trans_eq hn.2
    have hlt : (C ((n + 1 : R) ^ 2) * polynomial R n).degree <
        (X * polynomial R (n + 1)).degree := degree_lt_degree (by omega)
    exact ⟨hl.add_of_left hlt, by rw [natDegree_add_eq_left_of_degree_lt hlt, hld]⟩

/-- The monic Euler moment polynomial is a rescaled Meixner–Pollaczek polynomial. -/
lemma eval_polynomial_two_mul_I (n : ℕ) (x : ℝ) :
    (polynomial ℂ n).eval (2 * I * x) =
      (n ! : ℂ) * I ^ n *
        DLMF.OrthogonalPolynomials.meixnerPollaczek (1 / 2) (Real.pi / 2) n x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [DLMF.OrthogonalPolynomials.meixnerPollaczek_zero]
  | one =>
    rw [polynomial_one, eval_X,
      DLMF.OrthogonalPolynomials.meixnerPollaczek_one (by norm_num)]
    simp
    ring
  | more n hn hn1 =>
    rw [polynomial_add_two, eval_add, eval_mul, eval_X, eval_mul, eval_C, hn, hn1]
    have h := DLMF.OrthogonalPolynomials.meixnerPollaczek_recurrence
      (lam := (1 / 2 : ℂ)) (by norm_num) (Real.pi / 2) n x
    norm_num only [sin_pi_div_two, cos_pi_div_two, mul_one, mul_zero, add_zero] at h
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      pow_add, pow_one, pow_two]
    ring_nf at h ⊢
    simp only [I_sq]
    linear_combination (((n : ℂ) + 1) * (n ! : ℂ) * I ^ n) * h
end DLMF.BernoulliEuler.EulerMomentPolynomials

namespace DLMF.BernoulliEuler

/-- Euler numbers are the complex moments of the hyperbolic secant density. -/
lemma eulerNumber_eq_integral_moment (m : ℕ) :
    (eulerNumber m : ℂ) = ∫ x : ℝ, (2 * I * x) ^ m / (Real.cosh (Real.pi * x) : ℂ) := by
  rcases Nat.even_or_odd m with hm | hm
  · obtain ⟨k, hk⟩ := hm
    have hk' : m = 2 * k := by omega
    rw [hk']
    have heven : (∫ t : ℝ, t ^ (2 * k) / Real.cosh (Real.pi * t)) =
        2 * ∫ t in Set.Ioi (0 : ℝ), t ^ (2 * k) / Real.cosh (Real.pi * t) := by
      rw [← integral_comp_abs]
      congr 1
      funext t
      rw [show Real.pi * |t| = |Real.pi * t| by rw [abs_mul, abs_of_pos Real.pi_pos],
        Real.cosh_abs]
      rw [pow_mul, pow_mul, sq_abs]
    have hreal := eulerNumber_two_mul_eq_integral_sech k
    have hc := congrArg Complex.ofReal hreal
    push_cast at hc
    have hf : (fun x : ℝ => (2 * I * x) ^ (2 * k) / (Real.cosh (Real.pi * x) : ℂ)) =
        fun x : ℝ => (2 * I) ^ (2 * k) * ((x ^ (2 * k) / Real.cosh (Real.pi * x) : ℝ) : ℂ) := by
      funext x
      push_cast
      rw [mul_pow]
      ring
    rw [hf, integral_const_mul, integral_complex_ofReal, heven]
    push_cast
    rw [mul_pow, show I ^ (2 * k) = (-1 : ℂ) ^ k by rw [pow_mul, I_sq]]
    rw [pow_succ] at hc
    linear_combination hc
  · rw [eulerNumber_eq_zero_of_odd hm, Rat.cast_zero]
    let F : ℝ → ℂ := fun x => (2 * I * x) ^ m / (Real.cosh (Real.pi * x) : ℂ)
    have hneg (x : ℝ) : F (-x) = -F x := by
      simp only [F, Complex.ofReal_neg, mul_neg, hm.neg_pow, Real.cosh_neg, neg_div]
    have he : (∫ x, F x) = -(∫ x, F x) := by
      calc (∫ x, F x) = ∫ x, F (-x) := (integral_neg_eq_self F volume).symm
        _ = ∫ x, -F x := by simp only [hneg]
        _ = -(∫ x, F x) := integral_neg _
    have hz : (∫ x, F x) = 0 := by linear_combination (1 / 2 : ℂ) * he
    exact hz.symm

/-- A linear functional with Euler number moments is integration against the secant density. -/
lemma linearMap_eq_integral_euler_moment (L : ℂ[X] →ₗ[ℂ] ℂ)
    (hL : ∀ m, L (X ^ m) = (eulerNumber m : ℂ)) (P : ℂ[X]) :
    L P = ∫ x : ℝ, P.eval (2 * I * x) / (Real.cosh (Real.pi * x) : ℂ) := by
  have hi (P : ℂ[X]) :
      Integrable (fun x : ℝ => P.eval (2 * I * x) / (Real.cosh (Real.pi * x) : ℂ)) := by
    have h := RCLike.integrable_eval_polynomial_div_cosh Real.pi_pos (P.comp (C (2 * I) * X))
    exact h.congr (Filter.Eventually.of_forall fun x => by
      simp only [eval_comp, eval_mul, eval_C, eval_X]
      rfl)
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, hP, hQ, ← integral_add (hi P) (hi Q)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [eval_add, add_div]
  | monomial m a =>
    rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, hL, smul_eq_mul]
    simp only [eval_smul, eval_pow, eval_X, smul_eq_mul, mul_div_assoc]
    rw [integral_const_mul, ← eulerNumber_eq_integral_moment]

/-- The monic Euler moment polynomials diagonalize the Euler moment functional. -/
lemma linearMap_polynomial_mul (L : ℂ[X] →ₗ[ℂ] ℂ)
    (hL : ∀ m, L (X ^ m) = (eulerNumber m : ℂ)) (m n : ℕ) :
    L (EulerMomentPolynomials.polynomial ℂ m * EulerMomentPolynomials.polynomial ℂ n) =
      if m = n then (-1 : ℂ) ^ n * (n ! : ℂ) ^ 2 else 0 := by
  rw [linearMap_eq_integral_euler_moment L hL]
  have he (x : ℝ) : (EulerMomentPolynomials.polynomial ℂ m *
      EulerMomentPolynomials.polynomial ℂ n).eval (2 * I * x) / (Real.cosh (Real.pi * x) : ℂ) =
      ((m ! : ℂ) * I ^ m) * ((n ! : ℂ) * I ^ n) *
        (DLMF.OrthogonalPolynomials.meixnerPollaczek (1 / 2) (Real.pi / 2) m x *
          DLMF.OrthogonalPolynomials.meixnerPollaczek (1 / 2) (Real.pi / 2) n x /
            (Real.cosh (Real.pi * x) : ℂ)) := by
    rw [eval_mul, EulerMomentPolynomials.eval_polynomial_two_mul_I,
      EulerMomentPolynomials.eval_polynomial_two_mul_I]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_const_mul,
    DLMF.OrthogonalPolynomials.integral_meixnerPollaczek_mul_div_cosh]
  by_cases hmn : m = n
  · subst m
    simp only [↓reduceIte, mul_one]
    have hi : I ^ n * I ^ n = (-1 : ℂ) ^ n := by rw [← pow_add, ← two_mul, pow_mul, I_sq]
    calc (n ! : ℂ) * I ^ n * ((n ! : ℂ) * I ^ n) = (n ! : ℂ) ^ 2 * (I ^ n * I ^ n) := by ring
      _ = _ := by rw [hi]; ring
  · simp only [ite_eq_right hmn, mul_zero]

/-- DLMF 24.14.12: the Hankel determinant `det[E_{r + s}]_{r, s = 0}^{n}` equals
`(-1)^{n(n + 1) / 2} (∏_{k = 1}^n k!)²`. -/
@[dlmf 24.14.E12]
theorem det_hankel_eulerNumber (n : ℕ) :
    (Matrix.of fun r s : Fin (n + 1) => eulerNumber (r + s : ℕ)).det =
      (-1) ^ (n * (n + 1) / 2) * (∏ k ∈ Finset.Icc 1 n, (k ! : ℚ)) ^ 2 := by
  let L : ℂ[X] →ₗ[ℂ] ℂ := (Polynomial.basisMonomials ℂ).constr ℂ
    (fun m => (eulerNumber m : ℂ))
  have hL (m : ℕ) : L (X ^ m) = (eulerNumber m : ℂ) := by
    have h := (Polynomial.basisMonomials ℂ).constr_basis ℂ
      (fun m => (eulerNumber m : ℂ)) m
    simpa only [Polynomial.coe_basisMonomials, monomial_one_right_eq_X_pow, L] using h
  let p : Fin (n + 1) → ℂ[X] := fun i => EulerMomentPolynomials.polynomial ℂ i
  have hdeg (i : Fin (n + 1)) : (p i).natDegree = i :=
    (EulerMomentPolynomials.monic_polynomial_and_natDegree ℂ i).2
  have hmonic (i : Fin (n + 1)) : (p i).Monic :=
    (EulerMomentPolynomials.monic_polynomial_and_natDegree ℂ i).1
  have horth (i j : Fin (n + 1)) (hij : i ≠ j) : L (p i * p j) = 0 := by
    rw [linearMap_polynomial_mul L hL]
    exact ite_eq_right (fun h => hij (Fin.ext h))
  have hdet := Matrix.det_hankel_eq_prod_of_orthogonal_polynomials L p hdeg hmonic horth
  simp only [hL] at hdet
  have hnorm (i : Fin (n + 1)) : L ((p i) ^ 2) = (-1 : ℂ) ^ (i : ℕ) * ((i : ℕ) ! : ℂ) ^ 2 := by
    rw [pow_two, linearMap_polynomial_mul L hL]
    simp only [↓reduceIte]
  rw [Finset.prod_congr rfl (fun i _ => hnorm i), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow] at hdet
  have hsum : (∑ i : Fin (n + 1), (i : ℕ)) = n * (n + 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) (n + 1), Finset.sum_range_id]
    rw [Nat.add_sub_cancel, Nat.mul_comm]
  have hprod (N : ℕ) : (∏ i ∈ Finset.range (N + 1), (i ! : ℂ)) =
      ∏ i ∈ Finset.Icc 1 N, (i ! : ℂ) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.prod_range_succ, Finset.prod_Icc_succ_top (by omega), ih]
  rw [hsum, Fin.prod_univ_eq_prod_range (fun i => (i ! : ℂ)) (n + 1), hprod] at hdet
  apply Rat.cast_injective (α := ℂ)
  rw [Rat.cast_det]
  push_cast
  convert hdet using 1
  congr 1

end DLMF.BernoulliEuler
