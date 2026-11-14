/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Strict error bounds and divergence of the real erfc expansion

Andrews, Askey and Roy, *Special Functions*, Appendix C, pp. 613–614.
The normalized expansion is asymptotic, with a strictly enveloping remainder;
it is divergent as an infinite series at every fixed positive argument.
-/

@[expose] public section

open Filter Finset

namespace DLMF.Confluent.Real

/-- The normalized complementary-error expansion is strictly enveloped by its first
omitted term. Andrews–Askey–Roy, *Special Functions*, Appendix C, pp. 613–614
(synopsis AAR-C.1.1–C.2.2). Both remainder inequalities are strict. -/
theorem erfc_asymptotic_remainder_strict {x : ℝ} (hx : 0 < x) (N : ℕ) :
    let R := Real.sqrt Real.pi * x * Real.exp (x ^ 2) * TauCeti.Real.erfc x -
      ∑ k ∈ range N, (-1 : ℝ) ^ k * (ascPochhammer ℝ k).eval (1 / 2) / x ^ (2 * k)
    0 < (-1 : ℝ) ^ N * R ∧
      (-1 : ℝ) ^ N * R < (ascPochhammer ℝ N).eval (1 / 2) / x ^ (2 * N) := by
  sorry

/-- At fixed positive argument the erfc asymptotic terms grow without bound in modulus.
Andrews–Askey–Roy, *Special Functions*, Appendix C, pp. 613–614
(synopsis AAR-C.1.1–C.2.2). In particular the infinite series cannot converge. -/
theorem tendsto_erfc_asymptotic_term_norm {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ =>
      |(-1 : ℝ) ^ n * (ascPochhammer ℝ n).eval (1 / 2) / x ^ (2 * n)|)
      atTop atTop := by
  sorry

end DLMF.Confluent.Real
