/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Singularities

/-!
# Inhomogeneous rank-one Laurent coefficients and finite sectorial expansions

Olver, *Asymptotics and Special Functions*, Chapter 7, Theorem 14.1,
pp. 274–276, synopsis O-7.19. The coefficient operator is actual finite
Laurent coefficient arithmetic. The particular solution may depend on the
sector and the prescribed truncation; no global all-orders solution is asserted.
-/

@[expose] public noncomputable section

open Set Filter Complex Asymptotics
open scoped Topology Real BigOperators

namespace DLMF.AsymptoticApproximations.RankOneForcing

/-- Coefficients of the normalized inhomogeneous Laurent expansion. -/
def coefficient (pc qc rc : ℕ → ℂ) (α : ℂ) : ℕ → ℂ
  | 0 => rc 0 / qc 0
  | n + 1 =>
    (rc (n + 1) -
      ∑ s : Fin (n + 1), (qc (n + 1 - s) + (α - (s : ℂ)) * pc (n - s)) *
        coefficient pc qc rc α s -
      (if n = 0 then 0 else
        (α - ((n - 1 : ℕ) : ℂ)) * (α - (n : ℂ)) * coefficient pc qc rc α (n - 1))) /
      qc 0
  decreasing_by all_goals omega

/-- The source's initial forced coefficient. -/
@[simp] theorem coefficient_zero (pc qc rc : ℕ → ℂ) (α : ℂ) :
    coefficient pc qc rc α 0 = rc 0 / qc 0 := by
  rw [coefficient]

/-- The actual finite coefficient recursion. Olver, Chapter 7,
Theorem 14.1, pp. 274–276. -/
theorem coefficient_succ (pc qc rc : ℕ → ℂ) (α : ℂ) (n : ℕ) :
    coefficient pc qc rc α (n + 1) =
      (rc (n + 1) -
        ∑ s : Fin (n + 1), (qc (n + 1 - s) + (α - (s : ℂ)) * pc (n - s)) *
          coefficient pc qc rc α s -
        (if n = 0 then 0 else
          (α - ((n - 1 : ℕ) : ℂ)) * (α - (n : ℂ)) * coefficient pc qc rc α (n - 1))) /
        qc 0 := by
  rw [coefficient]

/-- The coefficient of `z⁻ⁿ` in the conjugated inhomogeneous differential operator
`A''+(p+2α/z)A'+(q+αp/z+α(α-1)/z²)A`. -/
def operatorCoefficient (pc qc : ℕ → ℂ) (α : ℂ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (∑ s : Fin (n + 1), qc (n - s) * a s) +
    (∑ s : Fin n, (α - (s : ℂ)) * pc (n - 1 - s) * a s) +
    if 2 ≤ n then (α - ((n - 2 : ℕ) : ℂ)) * (α - ((n - 1 : ℕ) : ℂ)) * a (n - 2) else 0

/-- The defining Laurent coefficient arithmetic. -/
theorem operatorCoefficient_def (pc qc : ℕ → ℂ) (α : ℂ) (a : ℕ → ℂ) (n : ℕ) :
    operatorCoefficient pc qc α a n =
      (∑ s : Fin (n + 1), qc (n - s) * a s) +
        (∑ s : Fin n, (α - (s : ℂ)) * pc (n - 1 - s) * a s) +
        if 2 ≤ n then (α - ((n - 2 : ℕ) : ℂ)) * (α - ((n - 1 : ℕ) : ℂ)) * a (n - 2)
        else 0 := rfl

/-- The recursion is the unique formal solution of the inhomogeneous coefficient
system. Olver, Chapter 7, §14.1, synopsis O-7.19. -/
theorem coefficient_operator_eq_and_unique (pc qc rc : ℕ → ℂ) (α : ℂ) (hq : qc 0 ≠ 0) :
    (∀ n, operatorCoefficient pc qc α (coefficient pc qc rc α) n = rc n) ∧
      (∀ a : ℕ → ℂ, (∀ n, operatorCoefficient pc qc α a n = rc n) →
        a = coefficient pc qc rc α) := by
  sorry

/-- A forced logarithmic-plane solution with any prescribed finite Laurent truncation
exists on closed annular sectors simultaneously progressive for both homogeneous roots
and their differences. The four unwrapped phase conditions give a concrete sufficient
domain. Olver, Chapter 7, Theorem 14.1, synopsis O-7.19. -/
theorem exists_finite_sectorial_expansion {p q r : ℂ → ℂ} {pc qc rc : ℕ → ℂ}
    {R : ℝ} {lam₁ lam₂ α : ℂ} (h : IsRankOneAtInfinity p q pc qc R lam₁ lam₂)
    (hq : qc 0 ≠ 0)
    (hr : ∀ z : ℂ, R < ‖z‖ → HasSum (fun n => rc n / z ^ n) (r z))
    {A B δ : ℝ} (hAB : A < B) (hδ : 0 < δ)
    (rootLog₁ rootLog₂ differenceLog₁ differenceLog₂ : ℂ)
    (hlogs : exp rootLog₁ = lam₁ ∧ exp rootLog₂ = lam₂ ∧
      exp differenceLog₁ = lam₁ - lam₂ ∧ exp differenceLog₂ = lam₂ - lam₁)
    (hphase : ∀ c ∈ ({rootLog₁, rootLog₂, differenceLog₁, differenceLog₂} : Set ℂ),
      -(3 * π / 2) + δ < A + c.im ∧ B + c.im < 3 * π / 2 - δ)
    (N : ℕ) :
    ∃ (R' : ℝ) (W : ℂ → ℂ), R < R' ∧ 0 < R' ∧
      AnalyticOnNhd ℂ W {w | R' < Real.exp w.re ∧ A ≤ w.im ∧ w.im ≤ B} ∧
      (∀ w : ℂ, R' < Real.exp w.re → A ≤ w.im → w.im ≤ B →
        deriv (deriv W) w - deriv W w + exp w * p (exp w) * deriv W w +
          exp (2 * w) * q (exp w) * W w = exp ((α + 2) * w) * r (exp w)) ∧
      (fun w => W w - exp (α * w) * ∑ n ∈ Finset.range N,
        coefficient pc qc rc α n * exp (-(n : ℂ) * w))
        =O[logSectorFilter A B 0] (fun w => exp ((α - N) * w)) := by
  sorry

end DLMF.AsymptoticApproximations.RankOneForcing
