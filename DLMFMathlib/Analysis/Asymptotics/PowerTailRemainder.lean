/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# The signed first-omitted-term remainder for power tails

Temme, *Special Functions*, Chapter 1, §1.3, pp. 10–14, applying
Theorem 1.3 to power functions (synopsis TEM-01-09–TEM-01-10).
The tail is the actual absolutely convergent scalar series.
-/

@[expose] public noncomputable section
namespace Real

/-- A positive power tail is strictly enveloped by its Bernoulli expansion.
Temme, Chapter 1, §1.3, Theorem 1.3 and its power-tail application,
synopsis TEM-01-09–TEM-01-10. The positive shift need not be an integer. -/
theorem exists_powerTail_remainder_factor {x s : ℝ} (hx : 0 < x) (hs : 1 < s)
    {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun k : ℕ => (x + k) ^ (-s)) ∧
    ∃ theta ∈ Set.Ioo (0 : ℝ) 1,
      (∑' k : ℕ, (x + k) ^ (-s)) = x ^ (1 - s) / (s - 1) + x ^ (-s) / 2 +
        (∑ j ∈ Finset.Ico 1 m, (bernoulli (2 * j) : ℝ) / (2 * j).factorial *
          (ascPochhammer ℝ (2 * j - 1)).eval s * x ^ (1 - s - 2 * j)) +
        theta * (bernoulli (2 * m) : ℝ) / (2 * m).factorial *
          (ascPochhammer ℝ (2 * m - 1)).eval s * x ^ (1 - s - 2 * m) := by
  sorry

end Real
