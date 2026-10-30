/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.Pochhammer

/-!
# Gaussian coefficients, q-numbers and q-derivatives
-/

@[expose] public noncomputable section

open Complex Finset Filter
open scoped Real Topology

namespace DLMF.QSeries

/-- Gaussian `q`-binomial coefficients `[n k]_q`, by the `q`-Pascal rule. -/
def qBinom (q : ℂ) : ℕ → ℕ → ℂ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)

/-- The `q`-derivative `δ_q f(x) = (f(x) - f(qx)) / ((1-q)x)` (Duverney (10.10)). -/
def qDeriv (q : ℂ) (f : ℂ → ℂ) (x : ℂ) : ℂ := (f x - f (q * x)) / ((1 - q) * x)

/-- The `q`-number `[n]_q = (1 - qⁿ)/(1 - q)`. -/
def qNum (q : ℂ) (n : ℕ) : ℂ := (1 - q ^ n) / (1 - q)

end DLMF.QSeries
