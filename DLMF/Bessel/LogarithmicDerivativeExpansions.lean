/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.LogarithmicMonodromy

/-!
# Differentiated lifted Hankel expansions

Olver, *Asymptotics and Special Functions*, Chapter 7, §5,
pp. 239–241, synopsis O-7.07. Partial sums include the exact exponential
prefactor. Differentiating in the logarithmic coordinate supplies one factor
`exp(w)` relative to differentiating in the original argument.
-/

@[expose] public noncomputable section

open Complex Filter Asymptotics DLMF.Core
open scoped Real Topology

namespace DLMF.Bessel

/-- The actual finite lifted Hankel expansion, with the same phase for both choices.
Olver, Chapter 7, §5, pp. 239–241, synopsis O-7.07. -/
def hankelOnLogPartialSum (ν : ℂ) (first : Bool) (N : ℕ) (w : ℂ) : ℂ :=
  let sign : ℂ := if first then 1 else -1
  (Real.sqrt (2 / π) : ℂ) * exp (-w / 2 + sign * I * (exp w - ν * π / 2 - π / 4)) *
    ∑ k ∈ Finset.range N, (sign * I) ^ k * largeArgumentCoefficient ν k * exp (-k * w)

/-- The defining finite expansion including its complete exponential prefactor. -/
theorem hankelOnLogPartialSum_def (ν : ℂ) (first : Bool) (N : ℕ) (w : ℂ) :
    hankelOnLogPartialSum ν first N w =
      let sign : ℂ := if first then 1 else -1
      (Real.sqrt (2 / π) : ℂ) * exp (-w / 2 + sign * I * (exp w - ν * π / 2 - π / 4)) *
        ∑ k ∈ Finset.range N,
          (sign * I) ^ k * largeArgumentCoefficient ν k * exp (-k * w) := rfl

/-- Termwise differentiated Hankel expansions on the full lifted sectors, to every finite
order. The `j=0` and `j=1` estimates give both the original and first derivative expansions.
Olver, Chapter 7, §5, pp. 239–241, synopsis O-7.07. -/
theorem isBigO_hankelOnLog_derivative_remainder (ν : ℂ) (first : Bool) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < 3 * π / 2) (N j : ℕ) (hj : j ≤ 1) :
    let sign : ℂ := if first then 1 else -1
    let H := if first then hankelH1OnLog ν else hankelH2OnLog ν
    IsBigO (comap (fun w : ℂ => w - sign * I * π / 2) (logSector (3 * π / 2 - δ)))
      (fun w => iteratedDeriv j (fun v => H v - hankelOnLogPartialSum ν first N v) w)
      (fun w : ℂ => exp (((j : ℂ) - N - 1 / 2) * w +
        sign * I * (exp w - ν * π / 2 - π / 4))) := by
  sorry

end DLMF.Bessel
