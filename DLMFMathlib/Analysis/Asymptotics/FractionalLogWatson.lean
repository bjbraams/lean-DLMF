/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonLog
public import Mathlib.RingTheory.Binomial

/-!
# Fractional logarithmic Watson scales

Olver, *Asymptotics and Special Functions*, Chapter 9, Theorem 1.2,
p. 324, synopsis O-9.02. Positive real logarithmic powers define a separate
scale; the inverse-log expansion does not replace its sharper finite remainder.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set Asymptotics
open scoped Topology
namespace Real.FractionalLogWatson

/-- The fractional logarithmic moment of Olver, Chapter 9, Theorem 1.2, p. 324. -/
def moment (a β x : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, Real.exp (-x * v) * v ^ (a - 1) * (Real.log (1 / v)) ^ β

/-- The defining fractional logarithmic moment integral. -/
theorem moment_def (a β x : ℝ) : moment a β x =
    ∫ v in (0 : ℝ)..1,
      Real.exp (-x * v) * v ^ (a - 1) * (Real.log (1 / v)) ^ β := rfl

/-- Absolute convergence for every real Laplace parameter. Olver Theorem 1.2. -/
theorem intervalIntegrable_moment {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (x : ℝ) :
    IntervalIntegrable
      (fun v => Real.exp (-x * v) * v ^ (a - 1) * (Real.log (1 / v)) ^ β)
      volume 0 1 := by
  sorry

/-- Every positive fractional logarithmic moment is strictly positive.
Olver, Chapter 9, Theorem 1.2, p. 324. -/
theorem moment_pos {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (x : ℝ) :
    0 < moment a β x := by
  sorry

/-- A local ramified expansion gives the sharper finite expansion in fractional
logarithmic moments. Olver, Chapter 9, Theorem 1.2, p. 324. -/
theorem isBigO_integral_sub_sum_moment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {a : ℕ → E} {lam μ β : ℝ}
    (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β)
    (hlocal : LocallyIntegrableOn f (Ioc 0 1))
    (hexp : ∀ N : ℕ, (fun v => f v - ∑ s ∈ Finset.range N,
      (v ^ (((s : ℝ) + lam) / μ - 1)) • a s) =O[𝓝[>] 0]
        (fun v : ℝ => v ^ (((N : ℝ) + lam) / μ - 1))) (N : ℕ) :
    (fun x => (∫ v in (0 : ℝ)..1,
      (Real.exp (-x * v) * (Real.log (1 / v)) ^ β) • f v) -
        ∑ s ∈ Finset.range N, moment (((s : ℝ) + lam) / μ) β x • a s) =O[atTop]
          (fun x => moment (((N : ℝ) + lam) / μ) β x) := by
  sorry

/-- The all-orders expansion of a fractional logarithmic moment in inverse
logarithms. Olver, Chapter 9, Theorem 1.2, p. 324. The coefficient uses the
canonical generalized binomial polynomial `Ring.choose`. -/
theorem isBigO_moment_sub_sum {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (N : ℕ) :
    (fun x : ℝ => moment a β x - x ^ (-a) * (Real.log x) ^ β *
      ∑ j ∈ Finset.range N,
        Ring.choose β j * (-1 : ℝ) ^ j * iteratedDeriv j Real.Gamma a /
          (Real.log x) ^ j) =O[atTop]
      (fun x : ℝ => x ^ (-a) * (Real.log x) ^ (β - N)) := by
  sorry

end Real.FractionalLogWatson
