/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Constructions

/-!
# Meromorphic equations admitting a separated scaling

An open family and a nonconstant scaling are essential: one fixed solution of
one fixed equation supplies no classification. The potential formulation retains
the quotient `P''/P`, avoiding a demand that the canonical solution itself be
meromorphic at an irregular singularity. Source: Olver, *Asymptotics and Special
Functions*, Chapter 12, Theorem 14.1, pp. 475–476.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace Complex

/-- A meromorphic potential admitting a nonconstant separated analytic scaling
on an open parameter family consists of one monomial and the Euler inverse-square
term. The normalization of the fixed canonical potential is retained as `alpha`.
Olver, Chapter 12, Theorem 14.1, pp. 475–476. -/
theorem exists_monomial_of_separated_scaling
    {f h Q ω : ℂ → ℂ} {U : Set ℂ} {u₀ : ℂ}
    (hU : IsOpen U) (hu₀ : u₀ ∈ U)
    (hf : MeromorphicAt f 0) (hh : MeromorphicAt h 0) (hQ : MeromorphicAt Q 0)
    (hfne : ¬ f =ᶠ[𝓝[≠] 0] 0)
    (hω : AnalyticOnNhd ℂ ω U) (hωne : ∀ u ∈ U, ω u ≠ 0)
    (hnonconstant : ¬ ω =ᶠ[𝓝 u₀] fun _ => ω u₀)
    (hscaled : ∀ u ∈ U,
      (fun z => u ^ 2 * f z + h z) =ᶠ[𝓝[≠] 0]
        (fun z => ω u ^ 2 * Q (z * ω u))) :
    ∃ (m : ℤ) (a b c α : ℂ), m ≠ -2 ∧ a ≠ 0 ∧ α ≠ 0 ∧
      f =ᶠ[𝓝[≠] 0] (fun z => a * z ^ m) ∧
      h =ᶠ[𝓝[≠] 0] (fun z => b * z ^ m + c / z ^ 2) ∧
      Q =ᶠ[𝓝[≠] 0] (fun z => α * z ^ m + c / z ^ 2) ∧
      ∀ᶠ u in 𝓝 u₀, α * ω u ^ (m + 2) = a * u ^ 2 + b := by
  sorry

/-- Conversely the monomial/inverse-square family separates on any nonzero
scaling branch. This is the exact differential substitution, so zeros of the
canonical solution cause no quotient problem. Olver, Chapter 12,
(14.05)–(14.07), p. 475. -/
theorem monomial_scaled_solution {P : ℂ → ℂ} {z u a b c α ω : ℂ} {m : ℤ}
    (hz : z ≠ 0) (hω : ω ≠ 0) (hP : AnalyticAt ℂ P (z * ω))
    (heq : deriv (deriv P) (z * ω) =
      (α * (z * ω) ^ m + c / (z * ω) ^ 2) * P (z * ω))
    (hscale : α * ω ^ (m + 2) = a * u ^ 2 + b) :
    deriv (deriv (fun t : ℂ => P (t * ω))) z =
      (u ^ 2 * (a * z ^ m) + b * z ^ m + c / z ^ 2) * P (z * ω) := by
  sorry

end Complex
