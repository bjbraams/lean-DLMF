/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Complex.Basic

/-!
# Real polynomials evaluated at real points of `ℂ`

The complexification of a real polynomial takes real values at real points.
-/

@[expose] public section

namespace Polynomial

/-- Evaluating the complexification of a real polynomial at a real point gives the real
value: `(P.map ℝ→ℂ).eval x = P.eval x`. -/
theorem eval_ofReal_map_algebraMap (P : ℝ[X]) (x : ℝ) :
    (P.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((P.eval x : ℝ) : ℂ) := by
  rw [eval_map]
  exact eval₂_at_apply (algebraMap ℝ ℂ) x

end Polynomial
