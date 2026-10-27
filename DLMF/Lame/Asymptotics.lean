/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Basic

/-!
# Lamé functions: asymptotic expansions of the eigenvalues (DLMF §29.7(i))

As `ν → ∞` (fixed `m` and `0 < k < 1`),
`a^m_ν(k²) ~ pκ - τ₀ - τ₁κ⁻¹ - τ₂κ⁻² - ⋯` with `κ = k(ν(ν+1))^{1/2}`, `p = 2m + 1`
(29.7.1–29.7.2), where `τ₀, …, τ₄` are given by 29.7.3, 29.7.4, 29.7.6–29.7.8; the same
expansion holds for `b^{m+1}_ν(k²)` because the difference is exponentially small (29.7.5).
The Poincaré expansion is stated as: there is a sequence `τ` with the given first five terms
such that for every `N` the remainder after `N` terms is `O(κ^{-N})`. The coefficients
(`lameKappa`, `lameTau0`–`lameTau4` in `DLMF.Lame.Basic`) were checked numerically
(remainders of `τ₀`–`τ₃` against eigenvalues from the recurrence 29.3.10 for
`ν = 100, 200, 400`). All statements are admitted. §29.7(ii) (Müller's formal
expansions of the Lamé functions) is descriptive and not acquired.
-/

@[expose] public section

open Filter Asymptotics
open scoped Real Topology

noncomputable section

namespace DLMF.Lame

/-- 29.7.1: the Poincaré expansion `a^m_ν(k²) ~ pκ - ∑ⱼ τⱼ κ^{-j}` as `ν → ∞`, `p = 2m + 1`,
with `τ₀, …, τ₄` as in 29.7.3, 29.7.4, 29.7.6–29.7.8. Admitted. -/
@[dlmf 29.7.E1]
theorem Real.lameAk_asymptotic {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∃ τ : ℕ → ℝ, τ 0 = lameTau0 (2 * m + 1) k ∧ τ 1 = lameTau1 (2 * m + 1) k ∧
      τ 2 = lameTau2 (2 * m + 1) k ∧ τ 3 = lameTau3 (2 * m + 1) k ∧
      τ 4 = lameTau4 (2 * m + 1) k ∧
      ∀ N : ℕ, (fun ν => Real.lameAk ν m k - ((2 * m + 1) * lameKappa ν k -
          ∑ j ∈ Finset.range N, τ j * lameKappa ν k ^ (-(j : ℤ)))) =O[atTop]
        fun ν => lameKappa ν k ^ (-(N : ℤ)) := by
  sorry

/-- 29.7.5: `b^{m+1}_ν(k²) - a^m_ν(k²) = O(ν^{m + 3/2} ((1 - k)/(1 + k))^ν)` as `ν → ∞`.
Admitted. -/
@[dlmf 29.7.E5]
theorem Real.lameBk_sub_lameAk_isBigO {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    (fun ν => Real.lameBk ν (m + 1) k - Real.lameAk ν m k) =O[atTop]
      fun ν => ν ^ ((m : ℝ) + 3 / 2) * ((1 - k) / (1 + k)) ^ ν := by
  sorry

/-- §29.7(i): the same Poincaré expansion holds for `b^{m+1}_ν(k²)`. Admitted. -/
@[dlmf 29.7.i]
theorem Real.lameBk_asymptotic {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) :
    ∃ τ : ℕ → ℝ, τ 0 = lameTau0 (2 * m + 1) k ∧ τ 1 = lameTau1 (2 * m + 1) k ∧
      τ 2 = lameTau2 (2 * m + 1) k ∧ τ 3 = lameTau3 (2 * m + 1) k ∧
      τ 4 = lameTau4 (2 * m + 1) k ∧
      ∀ N : ℕ, (fun ν => Real.lameBk ν (m + 1) k - ((2 * m + 1) * lameKappa ν k -
          ∑ j ∈ Finset.range N, τ j * lameKappa ν k ^ (-(j : ℤ)))) =O[atTop]
        fun ν => lameKappa ν k ^ (-(N : ℤ)) := by
  sorry

end DLMF.Lame
