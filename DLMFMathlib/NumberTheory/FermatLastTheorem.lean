/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.FLT.Basic

/-!
# The historical Fermat statement

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), §9.1,
pp. 9-1–9-2, synopsis RL-9.10. The full theorem is distinguished from the
special-exponent results in Mathlib.
-/

@[expose] public section

/-- Fermat's Last Theorem as cited in Rao–Lakshminarayanan §9.1, synopsis RL-9.10.
The upstream predicate requires all three natural bases to be nonzero. -/
theorem fermatLastTheorem : FermatLastTheorem := by
  sorry
