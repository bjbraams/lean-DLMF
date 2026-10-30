/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Basic

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion

/-!
# Difference equations (DLMF §2.9)

Asymptotic solutions of the three-term recurrence `w(n+2) + f(n) w(n+1) + g(n) w(n) = 0`
(2.9.1) when `f(n) ~ ∑ f_s n^{-s}`, `g(n) ~ ∑ g_s n^{-s}` (2.9.3), `g₀ ≠ 0`.

* `recurrence_iff_difference`: 2.9.1 ⇔ 2.9.2 (proved).
* `difference_distinct_roots_solutions`: the solutions 2.9.8 with the formal series 2.9.4–2.9.7
  when the roots of the characteristic equation 2.9.5 are distinct.
* `difference_recessive`: recessive and dominant solutions (§2.9(i)).
* `difference_coincident_sqrt`, `difference_coincident_power`, `difference_coincident_log`:
  coincident characteristic values, 2.9.9–2.9.13.

Expansions are `Asymptotics.HasAsymptoticExpansion atTop` in the scales
`n ↦ ρⁿ n^{α-s}` (2.9.8, 2.9.12) and `n ↦ ρⁿ e^{±κ√n} n^{α-s/2}` (2.9.9), with complex powers
`(n : ℂ) ^ (α - s)` (principal branch, `n > 0`). The coefficient `a_{s,j}` is `differenceCoeff`.
-/

@[expose] public noncomputable section

open Filter Asymptotics
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- DLMF 2.9.1 ⇔ 2.9.2: the three-term recurrence `w(n+2) + f(n)w(n+1) + g(n)w(n) = 0` is
equivalent to the second-order difference equation
`Δ²w(n) + (2 + f(n)) Δw(n) + (1 + f(n) + g(n)) w(n) = 0`; the two left sides are equal. -/
@[dlmf 2.9.E1, dlmf 2.9.E2]
theorem recurrence_eq_difference (f g w : ℕ → ℂ) (n : ℕ) :
    g2b_fwdDiff (g2b_fwdDiff w) n + (2 + f n) * g2b_fwdDiff w n + (1 + f n + g n) * w n =
      w (n + 2) + f n * w (n + 1) + g n * w n := by
  unfold g2b_fwdDiff; ring

/-- DLMF 2.9.1 ⇔ 2.9.2 for all `n = 0, 1, 2, …`. -/
@[dlmf 2.9.E1, dlmf 2.9.E2]
theorem recurrence_iff_difference (f g w : ℕ → ℂ) :
    IsRecurrenceSol f g w ↔
      ∀ n, g2b_fwdDiff (g2b_fwdDiff w) n + (2 + f n) * g2b_fwdDiff w n +
        (1 + f n + g n) * w n = 0 := by
  simp only [IsRecurrenceSol, recurrence_eq_difference]

/-- DLMF 2.9.4–2.9.8 (distinct characteristic values): let `f(n) ~ ∑ f_s n^{-s}` and
`g(n) ~ ∑ g_s n^{-s}` as `n → ∞` (2.9.3) with `g₀ ≠ 0` and `f₀² ≠ 4g₀`, and let `ρ` be a root
of `ρ² + f₀ρ + g₀ = 0` (2.9.5). Then 2.9.1 has a solution
`w(n) ~ ρⁿ n^{α} ∑ a_s n^{-s}` with `α` from 2.9.6 and `a_s` from 2.9.7. Applied to the two
roots it gives the linearly independent solutions `w₁`, `w₂`. -/
@[dlmf 2.9.E3, dlmf 2.9.E4, dlmf 2.9.E5, dlmf 2.9.E8, dlmf 2.9.i]
theorem difference_distinct_roots_solution {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (hf : HasAsymptoticExpansion atTop g2b_invPowScale fs f)
    (hg : HasAsymptoticExpansion atTop g2b_invPowScale gs g) (hg0 : gs 0 ≠ 0)
    (hdisc : fs 0 ^ 2 ≠ 4 * gs 0) {ρ : ℂ} (hρ : ρ ^ 2 + fs 0 * ρ + gs 0 = 0) :
    ∃ w : ℕ → ℂ, IsRecurrenceSol f g w ∧
      HasAsymptoticExpansion atTop (g2b_diffScale ρ (differenceExponent fs gs ρ))
        (differenceCoeff fs gs ρ) w := by
  sorry

/-- DLMF §2.9(i) (independence of the two solutions of 2.9.8): solutions with the expansions
2.9.8 for the two distinct roots `ρ₁ ≠ ρ₂` of 2.9.5 are linearly independent; their
Casoratian `w₁(n) w₂(n+1) - w₁(n+1) w₂(n)` is eventually nonzero. -/
@[dlmf 2.9.i]
theorem difference_distinct_roots_independent {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (hf : HasAsymptoticExpansion atTop g2b_invPowScale fs f)
    (hg : HasAsymptoticExpansion atTop g2b_invPowScale gs g) (hg0 : gs 0 ≠ 0)
    {ρ₁ ρ₂ : ℂ} (h12 : ρ₁ ≠ ρ₂) (hρ₁ : ρ₁ ^ 2 + fs 0 * ρ₁ + gs 0 = 0)
    (hρ₂ : ρ₂ ^ 2 + fs 0 * ρ₂ + gs 0 = 0) {w₁ w₂ : ℕ → ℂ}
    (hw₁ : HasAsymptoticExpansion atTop (g2b_diffScale ρ₁ (differenceExponent fs gs ρ₁))
      (differenceCoeff fs gs ρ₁) w₁)
    (hw₂ : HasAsymptoticExpansion atTop (g2b_diffScale ρ₂ (differenceExponent fs gs ρ₂))
      (differenceCoeff fs gs ρ₂) w₂) :
    ∀ᶠ n in atTop, w₁ n * w₂ (n + 1) - w₁ (n + 1) * w₂ n ≠ 0 := by
  sorry

/-- DLMF §2.9(i) (recessive and dominant solutions): in the situation of
`difference_distinct_roots_solution`, if `|ρ₂| > |ρ₁|`, or `|ρ₂| = |ρ₁|` and
`Re α₂ > Re α₁`, then `w₁` is recessive, `w₁(n)/w₂(n) → 0`, and it is unique up to a constant
factor: every solution `v` of 2.9.1 with `v(n)/w₂(n) → 0` is a multiple of `w₁`. -/
@[dlmf 2.9.i]
theorem difference_recessive {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (hf : HasAsymptoticExpansion atTop g2b_invPowScale fs f)
    (hg : HasAsymptoticExpansion atTop g2b_invPowScale gs g) (hg0 : gs 0 ≠ 0)
    {ρ₁ ρ₂ : ℂ} (h12 : ρ₁ ≠ ρ₂) (hρ₁ : ρ₁ ^ 2 + fs 0 * ρ₁ + gs 0 = 0)
    (hρ₂ : ρ₂ ^ 2 + fs 0 * ρ₂ + gs 0 = 0)
    (hdom : ‖ρ₁‖ < ‖ρ₂‖ ∨ (‖ρ₁‖ = ‖ρ₂‖ ∧
      (differenceExponent fs gs ρ₁).re < (differenceExponent fs gs ρ₂).re))
    {w₁ w₂ : ℕ → ℂ} (hs₁ : IsRecurrenceSol f g w₁) (hs₂ : IsRecurrenceSol f g w₂)
    (hw₁ : HasAsymptoticExpansion atTop (g2b_diffScale ρ₁ (differenceExponent fs gs ρ₁))
      (differenceCoeff fs gs ρ₁) w₁)
    (hw₂ : HasAsymptoticExpansion atTop (g2b_diffScale ρ₂ (differenceExponent fs gs ρ₂))
      (differenceCoeff fs gs ρ₂) w₂) :
    Tendsto (fun n => w₁ n / w₂ n) atTop (𝓝 0) ∧
      ∀ v : ℕ → ℂ, IsRecurrenceSol f g v → Tendsto (fun n => v n / w₂ n) atTop (𝓝 0) →
        ∃ c : ℂ, v = c • w₁ := by
  sorry

/-- DLMF 2.9.9–2.9.10 (coincident characteristic values, `2g₁ ≠ f₀f₁`): if `f₀² = 4g₀ ≠ 0`
with double root `ρ = -f₀/2` of 2.9.5, and `κ`, `α` satisfy `√g₀ κ = √(2f₀f₁ - 4g₁)` and
`4g₀α = g₀ + 2g₁` (any choice of the square roots, `κ ≠ 0`), then 2.9.1 has independent
solutions `w_j(n) ~ ρⁿ exp((-1)^j κ√n) n^{α} ∑ (-1)^{js} c_s n^{-s/2}`, `j = 1, 2`, with
`c₀ = 1` and the higher `c_s` determined by formal substitution. -/
@[dlmf 2.9.E9, dlmf 2.9.E10, dlmf 2.9.ii]
theorem difference_coincident_sqrt {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (hf : HasAsymptoticExpansion atTop g2b_invPowScale fs f)
    (hg : HasAsymptoticExpansion atTop g2b_invPowScale gs g) (hg0 : gs 0 ≠ 0)
    (hdisc : fs 0 ^ 2 = 4 * gs 0) (h1 : 2 * gs 1 ≠ fs 0 * fs 1) {κ α : ℂ}
    (hκ : κ ^ 2 * gs 0 = 2 * fs 0 * fs 1 - 4 * gs 1) (hα : 4 * gs 0 * α = gs 0 + 2 * gs 1) :
    ∃ c : ℕ → ℂ, c 0 = 1 ∧ ∃ w₁ w₂ : ℕ → ℂ,
      IsRecurrenceSol f g w₁ ∧ IsRecurrenceSol f g w₂ ∧
      HasAsymptoticExpansion atTop (g2b_sqrtScale (-fs 0 / 2) κ α (-1)) c w₁ ∧
      HasAsymptoticExpansion atTop (g2b_sqrtScale (-fs 0 / 2) κ α 1)
        (fun s => (-1) ^ s * c s) w₂ ∧
      ∀ᶠ n in atTop, w₁ n * w₂ (n + 1) - w₁ (n + 1) * w₂ n ≠ 0 := by
  sorry

/-- DLMF 2.9.11–2.9.12 (coincident characteristic values, `2g₁ = f₀f₁`): if `f₀² = 4g₀ ≠ 0`,
`ρ = -f₀/2`, and `α` is a root of `2g₀α² - (f₀f₁ + 2g₀)α + 2g₂ - f₀f₂ = 0` (2.9.11) whose
difference from the other root `α'` is not an integer, then 2.9.1 has a solution
`w(n) ~ ρⁿ n^{α} ∑ a_s n^{-s}` with `a₀ = 1` and the `a_s` satisfying 2.9.7 (whose left side
now vanishes). Applied to both roots it gives the independent solutions `w₁`, `w₂`. -/
@[dlmf 2.9.E11, dlmf 2.9.E12, dlmf 2.9.ii]
theorem difference_coincident_power {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (hf : HasAsymptoticExpansion atTop g2b_invPowScale fs f)
    (hg : HasAsymptoticExpansion atTop g2b_invPowScale gs g) (hg0 : gs 0 ≠ 0)
    (hdisc : fs 0 ^ 2 = 4 * gs 0) (h1 : 2 * gs 1 = fs 0 * fs 1) {α α' : ℂ}
    (hroots : ∀ x : ℂ, 2 * gs 0 * x ^ 2 - (fs 0 * fs 1 + 2 * gs 0) * x + 2 * gs 2 -
      fs 0 * fs 2 = 2 * gs 0 * (x - α) * (x - α'))
    (hint : ∀ m : ℤ, α' - α ≠ m) :
    ∃ a : ℕ → ℂ, IsDifferenceCoeffRel fs gs (-fs 0 / 2) α a ∧ ∃ w : ℕ → ℂ,
      IsRecurrenceSol f g w ∧ HasAsymptoticExpansion atTop (g2b_diffScale (-fs 0 / 2) α) a w := by
  sorry

/-- DLMF 2.9.12 for `j = 1` when `α₂ - α₁ ∈ {0, 1, 2, …}` (§2.9(ii)): with the hypotheses of
`difference_coincident_power` and roots `α₁`, `α₂` of 2.9.11 with `α₂ - α₁ = d ∈ ℕ`, 2.9.1 has
a solution `w₁(n) ~ ρⁿ n^{α₁} ∑ a_s n^{-s}` with `a₀ = 1` and the `a_s` satisfying 2.9.7. -/
@[dlmf 2.9.E12, dlmf 2.9.ii]
theorem difference_coincident_power_int {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (hf : HasAsymptoticExpansion atTop g2b_invPowScale fs f)
    (hg : HasAsymptoticExpansion atTop g2b_invPowScale gs g) (hg0 : gs 0 ≠ 0)
    (hdisc : fs 0 ^ 2 = 4 * gs 0) (h1 : 2 * gs 1 = fs 0 * fs 1) {α₁ α₂ : ℂ}
    (hroots : ∀ x : ℂ, 2 * gs 0 * x ^ 2 - (fs 0 * fs 1 + 2 * gs 0) * x + 2 * gs 2 -
      fs 0 * fs 2 = 2 * gs 0 * (x - α₁) * (x - α₂))
    {d : ℕ} (hd : α₂ - α₁ = d) :
    ∃ a : ℕ → ℂ, IsDifferenceCoeffRel fs gs (-fs 0 / 2) α₁ a ∧ ∃ w : ℕ → ℂ,
      IsRecurrenceSol f g w ∧ HasAsymptoticExpansion atTop (g2b_diffScale (-fs 0 / 2) α₁) a w := by
  sorry

/-- DLMF 2.9.13 (coincident characteristic values, `2g₁ = f₀f₁`, `α₂ - α₁ = d ∈ ℕ`): given the
solution `w₁` of `difference_coincident_power_int`, there is an independent solution
`w₂(n) ~ ρⁿ n^{α₂} ∑_{s ≠ d} b_s n^{-s} + c w₁(n) ln n`; that is, `w₂ - c w₁ ln` has the
expansion with coefficients `b_s` and `b_d = 0`. The normalization is `c = 1` when `d = 0` and
`b₀ = 1` when `d ≥ 1`. -/
@[dlmf 2.9.E13, dlmf 2.9.ii]
theorem difference_coincident_log {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (hf : HasAsymptoticExpansion atTop g2b_invPowScale fs f)
    (hg : HasAsymptoticExpansion atTop g2b_invPowScale gs g) (hg0 : gs 0 ≠ 0)
    (hdisc : fs 0 ^ 2 = 4 * gs 0) (h1 : 2 * gs 1 = fs 0 * fs 1) {α₁ α₂ : ℂ}
    (hroots : ∀ x : ℂ, 2 * gs 0 * x ^ 2 - (fs 0 * fs 1 + 2 * gs 0) * x + 2 * gs 2 -
      fs 0 * fs 2 = 2 * gs 0 * (x - α₁) * (x - α₂))
    {d : ℕ} (hd : α₂ - α₁ = d) {a : ℕ → ℂ} {w₁ : ℕ → ℂ} (hs₁ : IsRecurrenceSol f g w₁)
    (hw₁ : HasAsymptoticExpansion atTop (g2b_diffScale (-fs 0 / 2) α₁) a w₁) :
    ∃ (b : ℕ → ℂ) (c : ℂ) (w₂ : ℕ → ℂ), b d = 0 ∧ (d = 0 → c = 1) ∧ (1 ≤ d → b 0 = 1) ∧
      IsRecurrenceSol f g w₂ ∧
      HasAsymptoticExpansion atTop (g2b_diffScale (-fs 0 / 2) α₂) b
        (fun n => w₂ n - c * w₁ n * Real.log n) ∧
      ∀ᶠ n in atTop, w₁ n * w₂ (n + 1) - w₁ (n + 1) * w₂ n ≠ 0 := by
  sorry

end DLMF.AsymptoticApproximations
