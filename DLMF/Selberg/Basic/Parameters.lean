/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Selberg.Basic.Integrands
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Selberg product formula and convergence domain definitions
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set Filter
open scoped Real Topology

namespace DLMF.Selberg

/-- The right-hand side of Selberg's formula. -/
def selbergRHS (n : ℕ) (a b c : ℂ) : ℂ :=
  ∏ j : Fin n,
    Gamma (a + (j : ℕ) * c) * Gamma (b + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) /
      (Gamma (a + b + (n + j - 1 : ℕ) * c) * Gamma (1 + c))

/-- The domain of convergence in `c` for fixed `a`, `b`. -/
def cDomain (N : ℕ) (a b : ℂ) : Set ℂ :=
  {c | 0 < 1 + N * c.re ∧ 0 < a.re + ((N - 1 : ℕ) : ℝ) * c.re ∧
    0 < b.re + ((N - 1 : ℕ) : ℝ) * c.re}

end DLMF.Selberg
