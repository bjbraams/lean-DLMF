/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Asymptotics.LogarithmicSector
public import DLMF.Confluent.BasicProperties.Wronskians
public import DLMF.AsymptoticApproximations.ODE.Basic

/-!
# The full two-exponential regularized Kummer expansion on lifted sectors

Olver, *Asymptotics and Special Functions*, Chapter 7, §§9–10,
pp. 255–262, synopsis O-7.16–O-7.17. Each exact connection identity
continues globally in the logarithmic coordinate. Its two corresponding
closed sectors retain both absolute remainder scales, including exceptional
parameters where either reciprocal-Gamma coefficient vanishes.
-/

@[expose] public noncomputable section

open Complex Filter Asymptotics DLMF.Hypergeometric
open scoped Real Topology BigOperators

namespace DLMF.Confluent

/-- Both continued upper/lower Tricomi connection identities hold on the entire
logarithmic plane, with correlated shifts rather than principal reevaluation at `-z`.
Olver, Chapter 7, §9, synopsis O-7.16. -/
theorem regularizedConfluent_eq_tricomi_continued (a b w : ℂ) (upper : Bool) :
    let s : ℂ := if upper then 1 else -1
    regularizedHGFun {a} {b} (exp w) =
      exp (s * π * I * a) * kummerUContinuedOnLog a b w / Gamma (b - a) +
      exp (s * π * I * (a - b) + exp w) *
        kummerUContinuedOnLog (b - a) b (w - s * π * I) / Gamma a := by
  sorry

/-- Full two-exponential asymptotics on either lifted sector of opening `2π-2δ`.
The bound is absolute relative to both exponential scales and remains valid at zeros
of the combined leading expression. Olver, Chapter 7, §9, synopsis O-7.17. -/
theorem isBigO_regularizedConfluentOnLog_two_exponentials (a b : ℂ) (upper : Bool)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    let s : ℂ := if upper then 1 else -1
    let l := if upper then
        DLMF.AsymptoticApproximations.logSectorFilter (-π / 2 + δ) (3 * π / 2 - δ) 0
      else DLMF.AsymptoticApproximations.logSectorFilter (-3 * π / 2 + δ) (π / 2 - δ) 0
    (fun w : ℂ => regularizedHGFun {a} {b} (exp w) -
      (exp (exp w + (a - b) * w) / Gamma a *
        ∑ n ∈ Finset.range N, pochhammer (1 - a) n * pochhammer (b - a) n /
          (n.factorial : ℂ) * exp (-(n : ℂ) * w) +
      exp (s * π * I * a - a * w) / Gamma (b - a) *
        ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * pochhammer a n * pochhammer (1 + a - b) n /
          (n.factorial : ℂ) * exp (-(n : ℂ) * w)))
      =O[l] (fun w : ℂ =>
        Real.exp ((a.re - b.re - N) * w.re + (exp w).re) +
          Real.exp ((-a.re - N) * w.re)) := by
  sorry

end DLMF.Confluent
