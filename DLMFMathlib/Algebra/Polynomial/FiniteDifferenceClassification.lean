/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Algebra.Polynomial.FiniteDifference

/-!
# All solutions of a polynomial antidifference equation

Temme, *Special Functions*, Chapter 1, pp. 6–9, synopsis TEM-01-06.
The Bernoulli polynomial primitive is explicit; the remaining freedom is an
arbitrary function of period one, with no continuity assumption.
-/

@[expose] public section

namespace Polynomial

/-- Every solution of a polynomial antidifference equation is its explicit Bernoulli
primitive plus a function of period one. Temme, *Special Functions*, Chapter 1,
pp. 6–9, synopsis TEM-01-06. -/
theorem forall_eval_add_one_sub_eq_iff_exists_periodic
    {K : Type*} [Field K] [CharZero K] (P : K[X]) (F : K → K) :
    (∀ x : K, F (x + 1) - F x = P.eval x) ↔
      ∃ H : K → K, Function.Periodic H 1 ∧ ∀ x : K,
        F x = (∑ j ∈ Finset.range (P.natDegree + 1),
          P.coeff j / (j + 1 : K) * (bernoulli (j + 1)).eval₂ (algebraMap ℚ K) x) + H x := by
  sorry

end Polynomial
