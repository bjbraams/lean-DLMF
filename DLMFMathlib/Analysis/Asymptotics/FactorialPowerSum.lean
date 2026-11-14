/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Sums of real powers of factorial-scaled monomials

Olver, *Asymptotics and Special Functions*, Chapter 8, §8, pp. 307–309.
The positive-real sum `sum (x^n/n!)^p` has an exponential asymptotic expansion.
For nonintegral `p`, the corresponding entire function has the variable `z=x^p`;
no entireness in complex `x` is asserted for a nonintegral power at zero.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology Real Asymptotics

namespace Complex

/-- The power series with factorial-power denominators converges absolutely and
locally uniformly for positive real `p`. Olver, Chapter 8, §8, p. 307. -/
theorem summableLocallyUniformly_factorial_rpow {p : ℝ} (hp : 0 < p) :
    SummableLocallyUniformly (fun n : ℕ => fun z : ℂ =>
      z ^ n / ((n.factorial : ℝ) ^ p : ℝ)) := by
  sorry

/-- The factorial-power series is entire in its power-series variable. Its value at
`z=x^p`, for positive `x`, is Olver's factorial-power sum. Olver, Chapter 8, §8,
p. 307. -/
theorem analyticOnNhd_tsum_factorial_rpow {p : ℝ} (hp : 0 < p) :
    AnalyticOnNhd ℂ (fun z : ℂ =>
      ∑' n : ℕ, z ^ n / ((n.factorial : ℝ) ^ p : ℝ)) Set.univ := by
  sorry

end Complex

namespace Real

/-- Absolute convergence of Olver's positive-real factorial-power sum.
Olver, Chapter 8, §8, p. 307. -/
theorem summable_factorial_rpow {p : ℝ} (hp : 0 < p) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => (x ^ n / n.factorial) ^ p) := by
  sorry

/-- The first relative correction and a second-order remainder for the factorial-power
sum, with the source's restriction `p <= 4` retained. Olver, Chapter 8, §8,
pp. 307–309. -/
theorem isBigO_tsum_factorial_rpow {p : ℝ} (hp : 0 < p) (hp₄ : p ≤ 4) :
    (fun x : ℝ =>
      (∑' n : ℕ, (x ^ n / n.factorial) ^ p) /
        (exp (p * x) / (sqrt p * (2 * Real.pi * x) ^ ((p - 1) / 2))) -
      1 - (p ^ 2 - 1) / (24 * p * x)) =O[atTop] (fun x => x ^ (-2 : ℤ)) := by
  sorry

end Real
