/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.EulerTransformation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ordinary and Abel boundary forms of Euler transformation

Olver, *Asymptotics and Special Functions*, Chapter 14, Theorem 6.1,
pp. 537–539, synopsis O-14.05. Natural-order convergence is retained for
alternating series instead of replacing it by an unconditional HasSum.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology
namespace Asymptotics

/-- Euler's alternating transformation preserves every ordinarily convergent
Banach-valued series. Olver, Chapter 14, Theorem 6.1, pp. 537–539. -/
theorem tendsto_sum_alternating_fwdDiff_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℕ → E} {s : E}
    (ha : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n • a n)
      atTop (𝓝 s)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      ((-1 : ℝ) ^ n / 2 ^ (n + 1)) • ((fwdDiff (1 : ℕ))^[n] a) 0) atTop (𝓝 s) := by
  sorry

/-- At every real Abel parameter less than one, the transformed series equals
the coherent rationally substituted original power series. Olver, Chapter 14,
Theorem 6.1, pp. 537–539. Ordinary endpoint convergence suffices. -/
theorem hasSum_abel_alternating_fwdDiff_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a : ℕ → E} {s : E}
    (ha : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n • a n)
      atTop (𝓝 s)) {r : ℝ} (hr : r ∈ Set.Ico 0 1) :
    HasSum (fun n : ℕ => ((-r) ^ n / 2 ^ (n + 1)) • ((fwdDiff (1 : ℕ))^[n] a) 0)
      ((2 - r)⁻¹ • ∑' j : ℕ, (-(r / (2 - r))) ^ j • a j) := by
  sorry

/-- The full natural-order boundary form of Euler's translated inverse-power
series: if both series converge, their sums agree. Olver, Chapter 14,
Theorem 6.1, pp. 537–539. No absolute convergence is imposed. -/
theorem eq_of_tendsto_sum_eulerCoefficientTransform {a : ℕ → ℂ} {k z s t : ℂ}
    (hz : z ≠ 0) (hzk : z - k ≠ 0)
    (ha : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, a n / z ^ (n + 1))
      atTop (𝓝 s))
    (hb : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      eulerCoefficientTransform k a n / (z - k) ^ (n + 1)) atTop (𝓝 t)) :
    s = t := by
  sorry

/-- Two absolutely convergent inverse-power realizations of the same Euler
coefficient transform have the same sum, including convergent boundary points.
Olver, Chapter 14, Theorem 6.1, pp. 537–539. -/
theorem eq_of_hasSum_eulerCoefficientTransform {a : ℕ → ℂ} {k z s t : ℂ}
    (hz : z ≠ 0) (hzk : z - k ≠ 0)
    (ha : HasSum (fun n : ℕ => a n / z ^ (n + 1)) s)
    (hb : HasSum (fun n : ℕ => eulerCoefficientTransform k a n / (z - k) ^ (n + 1)) t) :
    s = t :=
  eq_of_tendsto_sum_eulerCoefficientTransform hz hzk ha.tendsto_sum_nat hb.tendsto_sum_nat

end Asymptotics
