/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.Basic.RelatedNumbers

/-!
# Integrality and the differential recurrence for tangent coefficients

Temme, *Special Functions* (1996), §1.1, (1.12), pp. 4–5.
The rational tangent numbers use the canonical DLMF normalization.
-/

@[expose] public section
open Finset
namespace DLMF.BernoulliEuler

/-- Differentiating `tan' = 1 + tan²` gives the tangent-number convolution,
Temme (1.12), synopsis TEM-01-03. -/
theorem tangentNumber_succ (n : ℕ) :
    tangentNumber (n + 1) = (if n = 0 then 1 else 0) +
      ∑ j ∈ range (n + 1), (n.choose j : ℚ) * tangentNumber j * tangentNumber (n - j) := by
  sorry

/-- Every odd tangent coefficient is a positive integer,
Temme (1.12), synopsis TEM-01-03. -/
theorem exists_pos_natCast_tangentNumber_odd (n : ℕ) :
    ∃ k : ℕ, 0 < k ∧ tangentNumber (2 * n + 1) = k := by
  sorry

end DLMF.BernoulliEuler
