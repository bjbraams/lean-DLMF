/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic

/-!
# The second nonresonant Kummer Frobenius solution

Andrews, Askey and Roy, *Special Functions*, §4.1, pp. 188–190,
synopsis AAR-4.1–4.4. The principal slit fixes the power z^(1-c), while
noninteger c makes both ordinary Kummer denominators regular.
-/

@[expose] public noncomputable section

open Complex

namespace DLMF.Confluent

/-- The shifted-power Kummer function solves the original confluent equation.
Andrews–Askey–Roy, §4.1, synopsis AAR-4.1–4.4. Together with the existing nonzero
`wronskian_kummerM_pair` this is the second Frobenius solution. -/
theorem kummerM_shifted_frobenius_ode (a c : ℂ) (hc : ∀ n : ℤ, c ≠ n)
    {z : ℂ} (hz : z ∈ slitPlane) :
    let f : ℂ → ℂ := fun w => w ^ (1 - c) * kummerM (1 + a - c) (2 - c) w
    z * deriv (deriv f) z + (c - z) * deriv f z - a * f z = 0 := by
  sorry

end DLMF.Confluent
