/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Dyson and Morris constant-term identities

Andrews, Askey and Roy, *Special Functions*, Theorems 8.8.1–8.8.2,
pp. 426–428 (synopsis AAR-8.7.1–8.9.1). A finite multivariate Laurent
polynomial is represented by the canonical additive monoid algebra of finitely
supported integer exponent vectors. The coefficient at the zero vector is its
constant term; no convergence or formal infinite expansion is involved.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace AddMonoidAlgebra

/-- Dyson's constant-term identity over a characteristic-zero field.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.8.1, pp. 426–427
(synopsis AAR-8.7.1–8.9.1). The empty-variable case has constant term one. -/
theorem coeff_zero_dyson {K : Type*} [Field K] [CharZero K]
    {n : ℕ} (a : Fin n → ℕ) :
    (∏ i : Fin n, ∏ j : Fin n,
      if i = j then (1 : AddMonoidAlgebra K (Fin n →₀ ℤ)) else
        (1 - single (Finsupp.single i (1 : ℤ) - Finsupp.single j (1 : ℤ)) (1 : K)) ^ a i).coeff 0 =
      ((∑ i, a i).factorial : K) / ∏ i, ((a i).factorial : K) := by
  sorry

/-- Morris's three-parameter constant-term identity.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.8.2, pp. 427–428
(synopsis AAR-8.7.1–8.9.1). All exponents are natural numbers, so the
expression is a finite Laurent polynomial, including when a parameter is zero. -/
theorem coeff_zero_morris {K : Type*} [Field K] [CharZero K]
    (n p q r : ℕ) :
    ((∏ i : Fin n,
      ((1 - single (Finsupp.single i (1 : ℤ)) (1 : K)) ^ p *
        (1 - single (Finsupp.single i (-1)) (1 : K)) ^ q)) *
      ∏ i : Fin n, ∏ j : Fin n,
        if i = j then (1 : AddMonoidAlgebra K (Fin n →₀ ℤ)) else
          (1 - single (Finsupp.single i (1 : ℤ) - Finsupp.single j (1 : ℤ)) (1 : K)) ^ r).coeff 0 =
      ∏ j ∈ range n,
        (((p + q + j * r).factorial : K) * ((j + 1) * r).factorial /
          (((p + j * r).factorial : K) * (q + j * r).factorial * r.factorial)) := by
  sorry

end AddMonoidAlgebra
