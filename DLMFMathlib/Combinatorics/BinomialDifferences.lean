/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Finite differences of generalized binomial coefficients

Andrews, Askey and Roy, *Special Functions*, §2.7, pp. 107–109
(synopsis AAR-2.7–2.8.2). Mathlib's canonical `Ring.choose` supplies polynomial
binomial coefficients. The statement holds in every commutative binomial ring,
including the integer, rational, real and complex coefficient cases.
-/

@[expose] public section

namespace Ring

/-- An `n`-fold finite difference lowers the lower binomial index by `n`.
Andrews–Askey–Roy, *Special Functions*, §2.7, pp. 107–109
(synopsis AAR-2.7–2.8.2). A difference of order greater than the polynomial
 degree is zero; this case is separate from truncated natural subtraction. -/
theorem sum_neg_one_pow_mul_choose_mul_choose_add_natCast {R : Type*}
    [CommRing R] [BinomialRing R] (x : R) (m n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : R) ^ k * (n.choose k : R) * choose (x + k) m) =
      if n ≤ m then (-1 : R) ^ n * choose x (m - n) else 0 := by
  sorry

end Ring
