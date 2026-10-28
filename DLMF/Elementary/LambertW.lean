/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Elementary.LambertW.BranchesAndCalculus
public import DLMF.Elementary.LambertW.Series

/-!
# Lambert W and Wright omega: DLMF §4.13

Neither Mathlib nor pinned TauCeti has Lambert W. A branch family is characterized
by the inverse equation, analytic continuation, branch indexing at `1`, and upper
boundary limits. Its existence is an explicit admitted acquisition theorem, not an
axiom or an unspecified opaque function. Lower cut values are separate. Nonprincipal
branches at zero are totalized to zero, outside all assertions for those branches.
The Wright omega equation uses DLMF's closed logarithm at its cut values.
-/
