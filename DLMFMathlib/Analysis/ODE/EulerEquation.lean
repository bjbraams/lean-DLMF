/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.Singularities
public import DLMFMathlib.Analysis.ODE.Wronskian
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Euler equations and elementary confluence examples

Kristensson, *Second Order Differential Equations*, §§4.1–4.2, pp. 43–48,
and Andrews, Askey and Roy, *Special Functions*, Appendix F, pp. 640–642.
Principal powers and logarithms are restricted to the slit plane. Exponentials
of an inverse coordinate are single-valued on the punctured plane.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology

noncomputable section

namespace Complex

/-- Kristensson, §4.2.1, p. 45, and AAR, Appendix F: a principal power solves
the Euler equation whose two indicial roots are `α,β`. -/
theorem euler_equation_cpow (α β : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    z ^ 2 * deriv (deriv (fun w : ℂ => w ^ α)) z +
      (1 - α - β) * z * deriv (fun w : ℂ => w ^ α) z + α * β * z ^ α = 0 := by
  sorry

/-- Kristensson, §4.2.1, p. 45, and AAR, Appendix F: a repeated indicial root
has the logarithmic second Euler solution. -/
theorem euler_equation_cpow_mul_log (α : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    z ^ 2 * deriv (deriv (fun w : ℂ => w ^ α * log w)) z +
      (1 - 2 * α) * z * deriv (fun w : ℂ => w ^ α * log w) z +
        α ^ 2 * (z ^ α * log z) = 0 := by
  sorry

/-- Kristensson, §4.2.1, p. 45: the Wronskian of the distinct-power Euler basis. -/
theorem wronskian_cpow (α β : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    z ^ α * deriv (fun w : ℂ => w ^ β) z -
      deriv (fun w : ℂ => w ^ α) z * z ^ β = (β - α) * z ^ (α + β - 1) := by
  sorry

/-- Kristensson, §4.2.1, p. 45: the Wronskian of the repeated-root Euler basis. -/
theorem wronskian_cpow_mul_log (α : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    z ^ α * deriv (fun w : ℂ => w ^ α * log w) z -
      deriv (fun w : ℂ => w ^ α) z * (z ^ α * log z) = z ^ (2 * α - 1) := by
  sorry

/-- Kristensson, §4.2.1, and AAR, Appendix F: distinct powers span the analytic
solutions of the Euler equation on a connected principal-branch domain. -/
theorem exists_euler_solution_eq_cpow_linear_combination {D : Set ℂ}
    {u : ℂ → ℂ} {α β : ℂ} (hD : IsOpen D) (hconn : IsPreconnected D)
    (hne : D.Nonempty) (hslit : D ⊆ slitPlane) (hαβ : α ≠ β)
    (hu : AnalyticOnNhd ℂ u D)
    (hode : ∀ z ∈ D, z ^ 2 * deriv (deriv u) z +
      (1 - α - β) * z * deriv u z + α * β * u z = 0) :
    ∃ A B : ℂ, ∀ z ∈ D, u z = A * z ^ α + B * z ^ β := by
  sorry

/-- Kristensson, §4.2.1, and AAR, Appendix F: a power and its logarithmic
multiple span the repeated-root Euler solution space. -/
theorem exists_euler_solution_eq_cpow_log_linear_combination {D : Set ℂ}
    {u : ℂ → ℂ} {α : ℂ} (hD : IsOpen D) (hconn : IsPreconnected D)
    (hne : D.Nonempty) (hslit : D ⊆ slitPlane) (hu : AnalyticOnNhd ℂ u D)
    (hode : ∀ z ∈ D, z ^ 2 * deriv (deriv u) z +
      (1 - 2 * α) * z * deriv u z + α ^ 2 * u z = 0) :
    ∃ A B : ℂ, ∀ z ∈ D, u z = A * z ^ α + B * z ^ α * log z := by
  sorry

/-- Kristensson, §4.2.3, pp. 47–48: the locally uniform coefficient limits
when two finite Euler singularities coalesce, with scaled exponent sums/products. -/
theorem tendstoLocallyUniformlyOn_coalescing_euler_coefficients
    {α β : ℂ → ℂ} {a k : ℂ}
    (hsum : Tendsto (fun ε => ε * (α ε + β ε)) (𝓝[≠] 0) (𝓝 0))
    (hprod : Tendsto (fun ε => ε ^ 2 * α ε * β ε) (𝓝[≠] 0) (𝓝 (k ^ 2))) :
    TendstoLocallyUniformlyOn
      (fun ε z => (1 - α ε - β ε) / (z - a) +
        (1 + α ε + β ε) / (z - a - ε))
      (fun z => 2 / (z - a)) (𝓝[≠] 0) {a}ᶜ ∧
    TendstoLocallyUniformlyOn
      (fun ε z => α ε * β ε * ε ^ 2 / ((z - a) ^ 2 * (z - a - ε) ^ 2))
      (fun z => k ^ 2 / (z - a) ^ 4) (𝓝[≠] 0) {a}ᶜ := by
  sorry

/-- Kristensson, §4.2.3: the exponential inverse-coordinate solutions after
coalescence. Replacing `k` by `-k` gives the second solution. -/
theorem inverse_exponential_equation (a k : ℂ) {z : ℂ} (hz : z ≠ a) :
    (z - a) ^ 4 * deriv (deriv (fun w => exp (I * k / (w - a)))) z +
      2 * (z - a) ^ 3 * deriv (fun w => exp (I * k / (w - a))) z +
        k ^ 2 * exp (I * k / (z - a)) = 0 := by
  sorry

/-- Kristensson, §4.2.3: nonzero scaled product gives an irregular singularity
at the coalesced point. -/
theorem linearODEIrregularAt_inverse_fourth_power (a : ℂ) {k : ℂ} (hk : k ≠ 0) :
    LinearODEIrregularAt ![fun z => k ^ 2 / (z - a) ^ 4, fun z => 2 / (z - a)] a := by
  sorry

/-- AAR, Appendix F, p. 642, corrected first-order example: the exponential has
the positive sign in `exp(c/(z-a))` for `(z-a)²u′+cu=0`. -/
theorem hasDerivAt_exp_const_div_sub (a c : ℂ) {z : ℂ} (hz : z ≠ a) :
    HasDerivAt (fun w => exp (c / (w - a)))
      (-(c / (z - a) ^ 2) * exp (c / (z - a))) z := by
  sorry

/-- AAR, Appendix F, p. 642: the first-order exponential example has an irregular
singularity when its coefficient is nonzero. -/
theorem linearODEIrregularAt_first_order_inverse_square (a : ℂ) {c : ℂ} (hc : c ≠ 0) :
    LinearODEIrregularAt ![fun z => c / (z - a) ^ 2] a := by
  sorry


/-- The two inverse exponentials have nonzero Wronskian when `k != 0`.
Kristensson, Chapter 4, §4.2.3, pp. 47–48. -/
theorem wronskian_inverse_exponentials (a k : ℂ) {z : ℂ} (hz : z ≠ a) :
    ODE.wronskian (fun w => exp (I * k / (w - a)))
      (fun w => exp (-(I * k / (w - a)))) z = 2 * I * k / (z - a) ^ 2 := by
  sorry

/-- The inverse exponentials span every solution of the coalesced irregular equation
on a connected ordinary domain. Kristensson, Chapter 4, §4.2.3, pp. 47–48. -/
theorem exists_inverse_exponential_linear_combination {U : Set ℂ}
    (hU : IsOpen U) (hconnected : IsPreconnected U) {a k : ℂ} (hk : k ≠ 0)
    (ha : ∀ z ∈ U, z ≠ a) {y : ℂ → ℂ}
    (hy : DifferentiableOn ℂ y U) (hy' : DifferentiableOn ℂ (deriv y) U)
    (hode : ∀ z ∈ U, (z - a) ^ 4 * deriv (deriv y) z +
      2 * (z - a) ^ 3 * deriv y z + k ^ 2 * y z = 0) :
    ∃ C D : ℂ, ∀ z ∈ U,
      y z = C * exp (I * k / (z - a)) + D * exp (-(I * k / (z - a))) := by
  sorry

/-- The two-finite-singularity Euler pullback is ordinary at infinity.
Kristensson, Chapter 4, (4.1), pp. 46–47. -/
theorem linearODEOrdinaryAtInfinity_mobius_euler (a b α β : ℂ) :
    LinearODEOrdinaryAtInfinity
      ![fun z => α * β * (a - b) ^ 2 / ((z - a) ^ 2 * (z - b) ^ 2),
        fun z => (1 - α - β) / (z - a) + (1 + α + β) / (z - b)] := by
  sorry

/-- A chosen logarithm of the Mobius coordinate gives a genuine analytic power
solution of the two-finite-singularity equation. Kristensson, Chapter 4,
(4.1), pp. 46–47. -/
theorem mobius_euler_equation_exp_log {U : Set ℂ} (hU : IsOpen U)
    {a b α β : ℂ} (hab : a ≠ b) (ha : ∀ z ∈ U, z ≠ a) (hb : ∀ z ∈ U, z ≠ b)
    {L : ℂ → ℂ} (hL : AnalyticOnNhd ℂ L U)
    (hexp : ∀ z ∈ U, exp (L z) = (z - a) / (z - b)) :
    ∀ z ∈ U, deriv (deriv (fun w => exp (α * L w))) z +
      ((1 - α - β) / (z - a) + (1 + α + β) / (z - b)) *
        deriv (fun w => exp (α * L w)) z +
      α * β * (a - b) ^ 2 / ((z - a) ^ 2 * (z - b) ^ 2) * exp (α * L z) = 0 := by
  sorry

/-- Distinct-exponent powers of the Mobius coordinate form a basis on a chosen
logarithm branch. Kristensson, Chapter 4, (4.1), pp. 46–47. -/
theorem exists_mobius_euler_linear_combination {U : Set ℂ}
    (hU : IsOpen U) (hconnected : IsPreconnected U)
    {a b α β : ℂ} (hab : a ≠ b) (hαβ : α ≠ β)
    (ha : ∀ z ∈ U, z ≠ a) (hb : ∀ z ∈ U, z ≠ b)
    {L y : ℂ → ℂ} (hL : AnalyticOnNhd ℂ L U)
    (hexp : ∀ z ∈ U, exp (L z) = (z - a) / (z - b))
    (hy : DifferentiableOn ℂ y U) (hy' : DifferentiableOn ℂ (deriv y) U)
    (hode : ∀ z ∈ U, deriv (deriv y) z +
      ((1 - α - β) / (z - a) + (1 + α + β) / (z - b)) * deriv y z +
      α * β * (a - b) ^ 2 / ((z - a) ^ 2 * (z - b) ^ 2) * y z = 0) :
    ∃ C D : ℂ, ∀ z ∈ U, y z = C * exp (α * L z) + D * exp (β * L z) := by
  sorry

/-- Equal exponents require the logarithmic second Mobius-Euler solution.
Kristensson, Chapter 4, (4.1), pp. 46–47. -/
theorem exists_mobius_euler_log_linear_combination {U : Set ℂ}
    (hU : IsOpen U) (hconnected : IsPreconnected U) {a b α : ℂ} (hab : a ≠ b)
    (ha : ∀ z ∈ U, z ≠ a) (hb : ∀ z ∈ U, z ≠ b)
    {L y : ℂ → ℂ} (hL : AnalyticOnNhd ℂ L U)
    (hexp : ∀ z ∈ U, exp (L z) = (z - a) / (z - b))
    (hy : DifferentiableOn ℂ y U) (hy' : DifferentiableOn ℂ (deriv y) U)
    (hode : ∀ z ∈ U, deriv (deriv y) z +
      ((1 - 2 * α) / (z - a) + (1 + 2 * α) / (z - b)) * deriv y z +
      α ^ 2 * (a - b) ^ 2 / ((z - a) ^ 2 * (z - b) ^ 2) * y z = 0) :
    ∃ C D : ℂ, ∀ z ∈ U, y z = exp (α * L z) * (C + D * L z) := by
  sorry

/-- The Euler power solution on any supplied analytic logarithm branch.
The equation is independent of the additive integral multiple in the logarithm.
Kristensson, Chapter 4, §4.2.1, p. 45; AAR, Appendix F. -/
theorem euler_equation_exp_log {U : Set ℂ} (hU : IsOpen U) {L : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L U) (hexp : ∀ z ∈ U, exp (L z) = z)
    (α β : ℂ) {z : ℂ} (hz : z ∈ U) :
    z ^ 2 * deriv (deriv (fun w => exp (α * L w))) z +
      (1 - α - β) * z * deriv (fun w => exp (α * L w)) z +
        α * β * exp (α * L z) = 0 := by
  sorry

/-- The repeated-root logarithmic solution on an arbitrary analytic log branch.
Kristensson, Chapter 4, §4.2.1, p. 45; AAR, Appendix F. -/
theorem euler_equation_exp_log_mul_log {U : Set ℂ} (hU : IsOpen U) {L : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L U) (hexp : ∀ z ∈ U, exp (L z) = z)
    (α : ℂ) {z : ℂ} (hz : z ∈ U) :
    z ^ 2 * deriv (deriv (fun w => exp (α * L w) * L w)) z +
      (1 - 2 * α) * z * deriv (fun w => exp (α * L w) * L w) z +
        α ^ 2 * (exp (α * L z) * L z) = 0 := by
  sorry

/-- The Wronskian of the distinct-root Euler functions on any logarithm branch.
Kristensson, Chapter 4, §4.2.1, p. 45. -/
theorem wronskian_exp_log {U : Set ℂ} (hU : IsOpen U) {L : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L U) (hexp : ∀ z ∈ U, exp (L z) = z)
    (α β : ℂ) {z : ℂ} (hz : z ∈ U) :
    exp (α * L z) * deriv (fun w => exp (β * L w)) z -
      deriv (fun w => exp (α * L w)) z * exp (β * L z) =
        (β - α) * exp ((α + β - 1) * L z) := by
  sorry

/-- The Wronskian of the repeated-root Euler functions on any logarithm branch.
Kristensson, Chapter 4, §4.2.1, p. 45. -/
theorem wronskian_exp_log_mul_log {U : Set ℂ} (hU : IsOpen U) {L : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L U) (hexp : ∀ z ∈ U, exp (L z) = z)
    (α : ℂ) {z : ℂ} (hz : z ∈ U) :
    exp (α * L z) * deriv (fun w => exp (α * L w) * L w) z -
      deriv (fun w => exp (α * L w)) z * (exp (α * L z) * L z) =
        exp ((2 * α - 1) * L z) := by
  sorry

/-- The distinct-root Euler basis spans every analytic solution on a connected
open logarithm domain, with unique constant coefficients. Kristensson,
Chapter 4, §4.2.1, p. 45; AAR, Appendix F. -/
theorem existsUnique_euler_solution_exp_log_linear_combination {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    {L : ℂ → ℂ} (hL : AnalyticOnNhd ℂ L U) (hexp : ∀ z ∈ U, exp (L z) = z)
    {α β : ℂ} (hαβ : α ≠ β) {u : ℂ → ℂ} (hu : AnalyticOnNhd ℂ u U)
    (hode : ∀ z ∈ U, z ^ 2 * deriv (deriv u) z +
      (1 - α - β) * z * deriv u z + α * β * u z = 0) :
    ∃! C : ℂ × ℂ, ∀ z ∈ U, u z = C.1 * exp (α * L z) + C.2 * exp (β * L z) := by
  sorry

/-- The repeated-root Euler basis spans every analytic solution on a connected
open logarithm domain, with unique constant coefficients. Kristensson,
Chapter 4, §4.2.1, p. 45; AAR, Appendix F. -/
theorem existsUnique_euler_solution_exp_log_mul_log_linear_combination {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    {L : ℂ → ℂ} (hL : AnalyticOnNhd ℂ L U) (hexp : ∀ z ∈ U, exp (L z) = z)
    {α : ℂ} {u : ℂ → ℂ} (hu : AnalyticOnNhd ℂ u U)
    (hode : ∀ z ∈ U, z ^ 2 * deriv (deriv u) z +
      (1 - 2 * α) * z * deriv u z + α ^ 2 * u z = 0) :
    ∃! C : ℂ × ℂ, ∀ z ∈ U,
      u z = C.1 * exp (α * L z) + C.2 * exp (α * L z) * L z := by
  sorry

end Complex
