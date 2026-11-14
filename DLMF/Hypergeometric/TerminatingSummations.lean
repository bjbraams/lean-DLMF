/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Saalschutz

/-!
# Terminating summations with finite denominator conditions

The finite Chu–Vandermonde and Pfaff–Saalschütz sums permit a lower parameter
whose first vanishing Pochhammer factor occurs after termination. Sources:
Duverney, *An Introduction to Hypergeometric Functions*, (4.51) and (4.70),
and Andrews–Askey–Roy, *Special Functions*, Chapter 2.
-/

@[expose] public noncomputable section

open Finset

namespace DLMF.Hypergeometric

/-- Chu–Vandermonde with exactly the finite denominator condition.
Duverney (4.51), synopsis DU-4.11; Andrews–Askey–Roy (2.2.3). -/
theorem sum_pochhammer_mul_neg_nat_div (N : ℕ) (a c : ℂ)
    (hc : ∀ k ≤ N, pochhammer c k ≠ 0) :
    (∑ k ∈ range (N + 1), pochhammer a k * pochhammer (-(N : ℂ)) k /
      (pochhammer c k * k.factorial)) = pochhammer (c - a) N / pochhammer c N := by
  sorry

/-- Pfaff–Saalschütz with finite denominator regularity, including later lower poles.
Duverney (4.70), synopsis DU-4.19; Andrews–Askey–Roy (2.2.6). -/
theorem pfaff_saalschutz_of_finite_regular (N : ℕ) (a b c : ℂ)
    (hc : ∀ k ≤ N, pochhammer c k ≠ 0)
    (hd : ∀ k ≤ N, pochhammer (1 + a + b - c - N) k ≠ 0) :
    (∑ k ∈ range (N + 1), pochhammer a k * pochhammer b k *
      pochhammer (-(N : ℂ)) k /
        (pochhammer c k * pochhammer (1 + a + b - c - N) k * k.factorial)) =
      pochhammer (c - a) N * pochhammer (c - b) N /
        (pochhammer c N * pochhammer (c - a - b) N) := by
  sorry

end DLMF.Hypergeometric
