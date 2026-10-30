/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Wronskians of two functions

`ODE.wronskian f g` is `f g' - g f'`. The scalar field and the normed-ring target
are independent, so real and complex functions and complex-valued functions of a real
variable share the same definition. The derivatives are totalized as in Mathlib;
results about solutions of differential equations assert differentiability separately.
-/

@[expose] public noncomputable section

namespace ODE

/-- The Wronskian `f g' - g f'` of two functions with values in a normed ring. -/
@[dlmf 1.13.E4]
def wronskian {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
    [NormedSpace 𝕜 E] (f g : 𝕜 → E) (z : 𝕜) : E :=
  f z * deriv g z - g z * deriv f z

end ODE
