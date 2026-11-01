/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Basic
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.Polynomial.Basic

/-!
# The Painlevé equations: elliptic form and Painlevé property (DLMF §32.2)

The elliptic form of `PVI` and the Painlevé property of the Painlevé equations, in the DLMF
normalization.

## Main results

* `IsPainleveVIOn.elliptic_form`: the elliptic form of `PVI` (DLMF 32.2.13–32.2.14).
* `IsPainleveIOn.exists_meromorphic`, `IsPainleveIIOn.exists_meromorphic`,
  `IsPainleveIVOn.exists_meromorphic`, `IsPainleveIIIOn.exists_meromorphic_exp`,
  `IsPainleveVOn.exists_meromorphic_exp`: the Painlevé property (DLMF §32.2(i)).

## Implementation notes

For `PIII` and `PV`, with their fixed singularity at `0`, the Painlevé property is stated for
`t ↦ w(eᵗ)`. The other §32.2 results (renormalizations, alternative and symmetric forms, the
coalescence cascade) are in `DLMF.Painleve.Basic.Transformations` and
`DLMF.Painleve.Basic.Coalescence`.
-/

@[expose] public noncomputable section

open Set Filter Complex
open scoped Topology

namespace DLMF.Painleve

/-- DLMF 32.2.13–32.2.14, the elliptic form of `PVI`. With the operator
`I = z(1-z) d²/dz² + (1-2z) d/dz - 1/4` (32.2.14) and
`Φ(z) = ∫_∞^{w(z)} dt/√(t(t-1)(t-z))`, a solution of `PVI` satisfies
`z(1-z) I Φ = √(w(w-1)(w-z)) (α + βz/w² + γ(z-1)/(w-1)² + (δ - 1/2) z(z-1)/(w-z)²)`.

Branch convention (made precise here; DLMF leaves it implicit): the path of integration is the
ray `t = w(z)/s`, `0 < s ≤ 1`, and the square root is the principal one, which is assumed to be
continuous along the ray (the polynomial stays in the slit plane); so
`Φ(z) = -∫₀¹ (w/s²) (P(w/s))^{-1/2} ds` with `P(t) = t(t-1)(t-z)`. -/
@[dlmf 32.2.E13, dlmf 32.2.E14]
theorem IsPainleveVIOn.elliptic_form {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveVIOn α β γ δ w U) (hU : IsOpen U)
    (hcut : ∀ z ∈ U, ∀ s : ℝ, 0 < s → s ≤ 1 →
      (w z / s) * (w z / s - 1) * (w z / s - z) ∈ Complex.slitPlane)
    {Φ : ℂ → ℂ}
    (hΦ : ∀ z ∈ U, Φ z = -∫ s in (0 : ℝ)..1, (w z / (s : ℂ) ^ 2) /
      ((w z / s) * (w z / s - 1) * (w z / s - z)) ^ (1 / 2 : ℂ)) :
    ∀ z ∈ U, z * (1 - z) * (z * (1 - z) * deriv (deriv Φ) z + (1 - 2 * z) * deriv Φ z -
        Φ z / 4) =
      (w z * (w z - 1) * (w z - z)) ^ (1 / 2 : ℂ) *
        (α + β * z / w z ^ 2 + γ * (z - 1) / (w z - 1) ^ 2 +
          (δ - 1 / 2) * z * (z - 1) / (w z - z) ^ 2) := by
  sorry

/-! ## The Painlevé property (§32.2(i)) -/

/-- DLMF §32.2(i): the Painlevé property of `PI` in its global form: every solution on a
connected open set is the restriction of a function meromorphic in the whole plane. -/
@[dlmf 32.2.i]
theorem IsPainleveIOn.exists_meromorphic {w : ℂ → ℂ} {U : Set ℂ} (h : IsPainleveIOn w U)
    (hU : IsOpen U) (hc : IsConnected U) :
    ∃ W : ℂ → ℂ, MeromorphicOn W univ ∧ EqOn W w U := by
  sorry

/-- DLMF §32.2(i): the Painlevé property of `PII`: every solution on a connected open set
extends to a function meromorphic in the whole plane. -/
@[dlmf 32.2.i]
theorem IsPainleveIIOn.exists_meromorphic {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIOn α w U) (hU : IsOpen U) (hc : IsConnected U) :
    ∃ W : ℂ → ℂ, MeromorphicOn W univ ∧ EqOn W w U := by
  sorry

/-- DLMF §32.2(i): the Painlevé property of `PIV`: every solution on a connected open set
extends to a function meromorphic in the whole plane. -/
@[dlmf 32.2.i]
theorem IsPainleveIVOn.exists_meromorphic {α β : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIVOn α β w U) (hU : IsOpen U) (hc : IsConnected U) :
    ∃ W : ℂ → ℂ, MeromorphicOn W univ ∧ EqOn W w U := by
  sorry

/-- DLMF §32.2(i): the Painlevé property of `PIII` (fixed singularity at `0`): for a solution
on a connected open set `U`, the function `t ↦ w(eᵗ)` extends to a function meromorphic in
the whole `t`-plane. -/
@[dlmf 32.2.i]
theorem IsPainleveIIIOn.exists_meromorphic_exp {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIIOn α β γ δ w U) (hU : IsOpen U) {T : Set ℂ} (hT : IsOpen T)
    (hTc : IsConnected T) (hTU : ∀ t ∈ T, Complex.exp t ∈ U) :
    ∃ W : ℂ → ℂ, MeromorphicOn W univ ∧ ∀ t ∈ T, W t = w (Complex.exp t) := by
  sorry

/-- DLMF §32.2(i): the Painlevé property of `PV` (fixed singularity at `0`): `t ↦ w(eᵗ)`
extends to a function meromorphic in the whole `t`-plane. -/
@[dlmf 32.2.i]
theorem IsPainleveVOn.exists_meromorphic_exp {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveVOn α β γ δ w U) (hU : IsOpen U) {T : Set ℂ} (hT : IsOpen T)
    (hTc : IsConnected T) (hTU : ∀ t ∈ T, Complex.exp t ∈ U) :
    ∃ W : ℂ → ℂ, MeromorphicOn W univ ∧ ∀ t ∈ T, W t = w (Complex.exp t) := by
  sorry

end DLMF.Painleve
