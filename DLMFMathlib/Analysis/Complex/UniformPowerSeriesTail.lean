/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Uniform power-series tails inside the radius of convergence

Olver, *Asymptotics and Special Functions*, Chapter 1, Theorem 3.1, p. 7,
synopsis O-1.03. A coefficient bound on an intermediate radius gives an
explicit geometric remainder throughout each smaller closed disk.
-/

@[expose] public section

namespace Complex

/-- An intermediate-radius coefficient bound controls every tail uniformly on the smaller
disk. Olver, Chapter 1, Theorem 3.1, p. 7, synopsis O-1.03. Banach-valued
coefficients are allowed and the smaller radius may be zero. -/
theorem exists_coeff_bound_and_norm_tsum_tail_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (a : ℕ → E) {r ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρσ : ρ < σ) (hσr : σ < r)
    (hs : ∀ z : ℂ, ‖z‖ < r → Summable (fun n : ℕ => z ^ n • a n)) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ n : ℕ, ‖a n‖ ≤ M / σ ^ n) ∧
      ∀ N : ℕ, ∀ z : ℂ, ‖z‖ ≤ ρ →
        Summable (fun n : ℕ => z ^ (n + N) • a (n + N)) ∧
          ‖∑' n : ℕ, z ^ (n + N) • a (n + N)‖ ≤
            M / (σ ^ N * (1 - ρ / σ)) * ‖z‖ ^ N := by
  sorry

end Complex
