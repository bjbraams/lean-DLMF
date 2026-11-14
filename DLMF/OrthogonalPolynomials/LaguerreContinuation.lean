/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.Classical
public import DLMF.OrthogonalPolynomials.Basic.PolynomialContinuation
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Polynomial continuation of Laguerre identities

The canonical finite polynomial `laguerreExtended` includes every complex parameter,
including values at which an unregularized hypergeometric expression degenerates.
Rodrigues's identity, the equation and recurrences are Olver, *Asymptotics and Special
Functions*, Chapter 2, §7, pp. 48–52, and Kristensson, *Second Order Differential
Equations*, Chapter 7, §§7.2–7.3, pp. 130–132. The locally uniform Jacobi limit is
Kristensson (7.9), p. 130, and Temme, *Special Functions*, Chapter 6, §6.10.
-/

@[expose] public noncomputable section

open Complex Filter
open scoped Topology

namespace DLMF.OrthogonalPolynomials

/-- Rodrigues's formula after polynomial continuation in the Laguerre parameter.
The variable is in the principal slit plane, so all powers share one logarithm.
Kristensson, Chapter 7, §7.2, pp. 130–132; Olver, Chapter 2, §7, pp. 48–49. -/
theorem laguerreExtended_rodrigues (α : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    laguerreExtended α n z =
      z ^ (-α) * exp z / n.factorial *
        iteratedDeriv n (fun t : ℂ => t ^ ((n : ℂ) + α) * exp (-t)) z := by
  sorry

/-- The polynomial continuation satisfies the Laguerre equation at every complex
argument, including the origin and exceptional parameters. Olver, Chapter 2, §7,
pp. 49–52. -/
theorem laguerreExtended_differential_equation (α : ℂ) (n : ℕ) (z : ℂ) :
    z * iteratedDeriv 2 (laguerreExtended α n) z +
      (α + 1 - z) * deriv (laguerreExtended α n) z + n * laguerreExtended α n z = 0 := by
  sorry

/-- The derivative identity holds for every complex Laguerre parameter.
Olver, Chapter 2, §7.4, pp. 50–52. -/
theorem deriv_laguerreExtended (α : ℂ) (n : ℕ) (z : ℂ) :
    deriv (laguerreExtended α (n + 1)) z = -laguerreExtended (α + 1) n z := by
  sorry

/-- The polynomial three-term Laguerre recurrence, including exceptional complex
parameters. Indices start at `n,n+1,n+2` to avoid a negative-degree convention.
Olver, Chapter 2, §7.4, pp. 50–52. -/
theorem laguerreExtended_recurrence (α : ℂ) (n : ℕ) (z : ℂ) :
    (n + 2 : ℂ) * laguerreExtended α (n + 2) z =
      (2 * n + α + 3 - z) * laguerreExtended α (n + 1) z -
        (n + α + 1) * laguerreExtended α n z := by
  sorry

/-- The `n`th derivative is `(-1)^n`, so the polynomial always has degree exactly
`n`, independently of its parameter. Olver, Chapter 2, §7, pp. 48–49. -/
theorem iteratedDeriv_laguerreExtended_self (α : ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (laguerreExtended α n) z = (-1 : ℂ) ^ n := by
  sorry

/-- The Jacobi-to-Laguerre limit holds locally uniformly in the complex argument
for every complex parameter, using the genuine polynomial continuations on both
sides. Kristensson (7.9), p. 130; Temme, Chapter 6, §6.10. -/
theorem tendstoLocallyUniformly_jacobiExtended_laguerreExtended (α : ℂ) (n : ℕ) :
    TendstoLocallyUniformly
      (fun b : ℝ => fun z : ℂ => jacobiExtended α b n (1 - 2 * z / b))
      (laguerreExtended α n) atTop := by
  sorry

/-- Every monomial coefficient in the Jacobi-to-Laguerre limit converges. At the
origin its `k`th derivative is `k!` times that coefficient, so the derivative
formulation is independent of a second polynomial representation.
Kristensson (7.9), p. 130; Temme, Chapter 6, §6.10. -/
theorem tendsto_iteratedDeriv_jacobiExtended_laguerreExtended
    (α : ℂ) (n k : ℕ) :
    Tendsto (fun b : ℝ =>
      iteratedDeriv k (fun z : ℂ => jacobiExtended α b n (1 - 2 * z / b)) 0)
      atTop (𝓝 (iteratedDeriv k (laguerreExtended α n) 0)) := by
  sorry

end DLMF.OrthogonalPolynomials
