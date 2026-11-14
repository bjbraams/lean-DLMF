/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Inclusion theorems for Cesàro and Abel summation

Andrews, Askey and Roy, *Special Functions*, Appendix B, Theorems B.1.1–B.1.2
and §B.2 (synopsis AAR-B.1.1–B.1.6 and AAR-B.2–B.3). Ordered partial sums,
instead of unconditional `HasSum`, express convergence of the original series.
The statements use Mathlib sums and filters without a duplicate summability predicate.
-/

@[expose] public section

open Filter Finset
open scoped Topology

namespace Complex

/-- Abel's theorem in its uniform closed-radius form. At the boundary one uses the
ordered series sum, which can differ from the unconditional totalized `tsum`.
Andrews–Askey–Roy, *Special Functions*, Theorem B.1.1, p. 599
(synopsis AAR-B.1.1–B.1.6). -/
theorem tendstoUniformlyOn_partial_powerSeries_of_tendsto_sum {a : ℕ → ℂ} {S : ℂ}
    (h : Tendsto (fun N => ∑ n ∈ range N, a n) atTop (𝓝 S)) :
    TendstoUniformlyOn (fun N (x : ℝ) => ∑ n ∈ range N, a n * (x : ℂ) ^ n)
      (fun x : ℝ => if x = 1 then S else ∑' n, a n * (x : ℂ) ^ n)
      atTop (Set.Icc (0 : ℝ) 1) := by
  sorry

/-- A series summable by the first Cesàro method has the same Abel sum.
Andrews–Askey–Roy, *Special Functions*, Theorem B.1.2, p. 600
(synopsis AAR-B.1.1–B.1.6). -/
theorem tendsto_tsum_powerSeries_of_tendsto_cesaro {a : ℕ → ℂ} {S : ℂ}
    (h : Tendsto (fun N : ℕ =>
      (∑ n ∈ range (N + 1), ∑ k ∈ range (n + 1), a k) / (N + 1 : ℂ)) atTop (𝓝 S)) :
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, Summable (fun n => a n * (x : ℂ) ^ n)) ∧
      Tendsto (fun x : ℝ => ∑' n, a n * (x : ℂ) ^ n) (𝓝[<] 1) (𝓝 S) := by
  sorry

/-- Inclusion of generalized Cesàro methods: increasing a real order greater than `-1`
preserves every sum. Andrews–Askey–Roy, *Special Functions*, §B.2, pp. 602–603
(synopsis AAR-B.2–B.3). -/
theorem tendsto_cesaro_order_of_lt {a : ℕ → ℂ} {S : ℂ} {α β : ℝ}
    (hα : -1 < α) (hαβ : α < β)
    (h : Tendsto (fun N : ℕ =>
      (N.factorial : ℂ) / (ascPochhammer ℂ N).eval ((α : ℂ) + 1) *
        ∑ k ∈ range (N + 1),
          (ascPochhammer ℂ (N - k)).eval ((α : ℂ) + 1) /
            (N - k).factorial * a k) atTop (𝓝 S)) :
    Tendsto (fun N : ℕ =>
      (N.factorial : ℂ) / (ascPochhammer ℂ N).eval ((β : ℂ) + 1) *
        ∑ k ∈ range (N + 1),
          (ascPochhammer ℂ (N - k)).eval ((β : ℂ) + 1) /
            (N - k).factorial * a k) atTop (𝓝 S) := by
  sorry

end Complex
