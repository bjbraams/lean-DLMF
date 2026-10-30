/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Shifted factorials, Jackson integrals and q-gamma definitions
-/

@[expose] public noncomputable section

open Complex Finset Filter
open scoped Real Topology

namespace DLMF.QSeries

/-- The finite `q`-Pochhammer symbol `(a;q)_n`. -/
@[dlmf 17.2.E1]
def qPochhammer (a q : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => qPochhammer a q n * (1 - a * q ^ n)

/-- The infinite `q`-Pochhammer symbol `(a;q)_∞`. -/
@[dlmf 17.2.E4]
def qPochhammerInf (a q : ℂ) : ℂ :=
  ∏' k : ℕ, (1 - a * q ^ k)

/-- Jackson's `q`-integral `∫_0^a f(t)\,d_q t` (AAR §10.1). -/
@[dlmf 17.2.E46]
def jacksonIntegral (q a : ℂ) (f : ℂ → ℂ) : ℂ :=
  a * (1 - q) * ∑' n : ℕ, f (a * q ^ n) * q ^ n

/-- The `q`-gamma function (AAR §10.3):
`Γ_q(x) = (q;q)_∞ / (q^x;q)_∞ · (1-q)^{1-x}`. -/
@[dlmf 5.18.E4]
def qGamma (q x : ℂ) : ℂ :=
  qPochhammerInf q q / qPochhammerInf (q ^ x) q * (1 - q) ^ (1 - x)

end DLMF.QSeries
