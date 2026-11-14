/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import DLMFMathlib.Algebra.Polynomial.CompositionCoefficients
import Mathlib.Tactic

/-!
# Faà di Bruno's formula indexed by multiplicities

The `n`th derivative of a scalar composite is a finite sum indexed by the multiplicities
of the positive-order derivatives of the inner function. The sum of their orders with
these multiplicities is `n`. Local `Cⁿ` regularity suffices; order zero is included.

Mathlib's ordered-partition formula first shows that a composite derivative depends only
on finite Taylor data. Polynomial Taylor jets then reduce the coefficient calculation
to the multinomial theorem. The polynomial derivative values use TauCeti's
`Polynomial.iteratedDeriv_eval_zero`; the smoothness API is Mathlib's
`Polynomial.contDiff_aeval`. No upstream proof body is copied.

* `iteratedDeriv_comp_eq_of_forall_iteratedDeriv_eq`: comparison of finite derivative data.
* `iteratedDeriv_comp_eq_sum_multiplicities`: Faà di Bruno's multiplicity formula.
-/

public noncomputable section

open Finset Polynomial
open scoped Nat

/-- Equal finite derivative data for inner and outer functions give equal composite derivatives.
The inner constant terms may differ, since outer derivatives are taken at the corresponding
inner values. -/
lemma iteratedDeriv_comp_eq_of_forall_iteratedDeriv_eq
    {K : Type*} [NontriviallyNormedField K] {f g F G : K → K} {x y : K} {n : ℕ}
    (hf : ContDiffAt K n f (g x)) (hg : ContDiffAt K n g x)
    (hF : ContDiffAt K n F (G y)) (hG : ContDiffAt K n G y)
    (hfg : ∀ k ≤ n, iteratedDeriv k f (g x) = iteratedDeriv k F (G y))
    (hgg : ∀ k, 1 ≤ k → k ≤ n → iteratedDeriv k g x = iteratedDeriv k G y) :
    iteratedDeriv n (f ∘ g) x = iteratedDeriv n (F ∘ G) y := by
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hf hg le_rfl,
    iteratedDeriv_comp_eq_sum_orderedFinpartition hF hG le_rfl]
  apply Finset.sum_congr rfl
  intro c _
  rw [hfg c.length c.length_le]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact hgg _ (c.partSize_pos j) (c.partSize_le j)

/-- Faà di Bruno's formula indexed by derivative multiplicities, including order zero.
The functions need only be `Cⁿ` at the points where their derivatives are evaluated. -/
lemma iteratedDeriv_comp_eq_sum_multiplicities
    {K : Type*} [NontriviallyNormedField K] [CharZero K] {f g : K → K}
    (n : ℕ) {x : K} (hf : ContDiffAt K n f (g x)) (hg : ContDiffAt K n g x) :
    iteratedDeriv n (f ∘ g) x =
      ∑ m ∈ (Finset.univ : Finset (Fin n → Fin (n + 1))).filter
          (fun m => ∑ j : Fin n, (j.val + 1) * (m j).val = n),
        ((n ! : K) / ∏ j : Fin n, ((m j).val ! : K)) *
          iteratedDeriv (∑ j : Fin n, (m j).val) f (g x) *
          ∏ j : Fin n, (iteratedDeriv (j.val + 1) g x / ((j.val + 1) ! : K)) ^ (m j).val := by
  classical
  let P : K[X] := ∑ k ∈ range (n + 1), monomial k (iteratedDeriv k f (g x) / (k ! : K))
  let Q : K[X] := ∑ j : Fin n, monomial (j.val + 1)
    (iteratedDeriv (j.val + 1) g x / ((j.val + 1) ! : K))
  have hP (k : ℕ) (hk : k ≤ n) : P.coeff k = iteratedDeriv k f (g x) / (k ! : K) := by
    simp [P, finsetSum_coeff, coeff_monomial, hk]
  have hQ0 : Q.eval 0 = 0 := by
    dsimp only [Q]
    rw [eval_finsetSum]
    simp [eval_monomial, pow_succ]
  have hQ (k : ℕ) (hk0 : 1 ≤ k) (hkn : k ≤ n) :
      Q.coeff k = iteratedDeriv k g x / (k ! : K) := by
    let j : Fin n := ⟨k - 1, by omega⟩
    have hj : j.val + 1 = k := by dsimp only [j]; omega
    dsimp only [Q]
    rw [finsetSum_coeff]
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro i _ hij
      have hi : i.val + 1 ≠ k := by
        intro h
        exact hij (Fin.ext (by omega))
      simp [coeff_monomial, hi]
    · simp
  have hPd (k : ℕ) (hk : k ≤ n) :
      iteratedDeriv k (fun t => P.eval t) 0 = iteratedDeriv k f (g x) := by
    rw [Polynomial.iteratedDeriv_eval_zero, hP k hk]
    exact mul_div_cancel₀ _ (by exact_mod_cast Nat.factorial_ne_zero k)
  have hQd (k : ℕ) (hk0 : 1 ≤ k) (hkn : k ≤ n) :
      iteratedDeriv k (fun t => Q.eval t) 0 = iteratedDeriv k g x := by
    rw [Polynomial.iteratedDeriv_eval_zero, hQ k hk0 hkn]
    exact mul_div_cancel₀ _ (by exact_mod_cast Nat.factorial_ne_zero k)
  have he : iteratedDeriv n (f ∘ g) x =
      iteratedDeriv n ((fun t => P.eval t) ∘ (fun t => Q.eval t)) 0 := by
    apply iteratedDeriv_comp_eq_of_forall_iteratedDeriv_eq hf hg
      (by simpa using (P.contDiff_aeval (𝕜 := K) n).contDiffAt)
      (by simpa using (Q.contDiff_aeval (𝕜 := K) n).contDiffAt)
    · intro k hk
      rw [hQ0]
      exact (hPd k hk).symm
    · intro k hk0 hkn
      exact (hQd k hk0 hkn).symm
  rw [he]
  have hpq : ((fun t => P.eval t) ∘ (fun t => Q.eval t)) = fun t => (P.comp Q).eval t := by
    funext t
    simp
  rw [hpq, Polynomial.iteratedDeriv_eval_zero]
  have hcomp : P.comp Q = ∑ k ∈ range (n + 1), C (iteratedDeriv k f (g x) / (k ! : K)) * Q ^ k := by
    simp only [P, Polynomial.sum_comp, monomial_comp]
  rw [hcomp]
  dsimp only [Q]
  rw [coeff_sum_powers_sum_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hspec := Nat.multinomial_spec (univ : Finset (Fin n)) (fun j => (m j).val)
  have hs : (∏ j : Fin n, ((m j).val ! : K)) *
      (Nat.multinomial univ (fun j => (m j).val) : K) =
        ((∑ j : Fin n, (m j).val) ! : K) := by exact_mod_cast hspec
  have hprod : (∏ j : Fin n, ((m j).val ! : K)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast Nat.factorial_ne_zero (m j).val
  have hfac : ((∑ j : Fin n, (m j).val) ! : K) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (∑ j : Fin n, (m j).val)
  have hm : (Nat.multinomial univ (fun j => (m j).val) : K) =
      ((∑ j : Fin n, (m j).val) ! : K) / (∏ j : Fin n, ((m j).val ! : K)) := by
    apply (eq_div_iff hprod).mpr
    simpa only [mul_comm] using hs
  rw [hm]
  field_simp [hfac, hprod]
