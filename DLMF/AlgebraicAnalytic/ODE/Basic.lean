/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order

/-!
# Linear second-order differential equations: definitions (DLMF §1.13)

* `IsLinODE2SolOn f g r w D` (1.13.1, 1.13.8): `w'' + f w' + g w = r` on `D`, with genuine
  differentiability of `w` and of `w'` at every point of `D` (so the totalized `deriv` cannot
  make a nonsolution satisfy the equation); `r = 0` is the homogeneous equation 1.13.1.
* `IsFundamentalPair f g w₁ w₂ D` (1.13.2).
* `wronskian w₁ w₂` (1.13.4) and the `n`-argument Wronskian `wronskianN`.
* `schwarzian z ζ` (1.13.20): `{z, ζ} = z'''/z' - (3/2)(z''/z')²`, derivatives with respect
  to `ζ`.
* The Sturm–Liouville equation 1.13.26 (`IsSturmLiouvilleSolOn`), the unmixed and periodic
  boundary conditions 1.13.27–1.13.28 and the eigenvalues of a regular Sturm–Liouville system.
-/

@[expose] public noncomputable section

open Set

namespace DLMF.AlgebraicAnalytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- DLMF 1.13.1 and 1.13.8: `w` solves `w'' + f(z) w' + g(z) w = r(z)` on `D`: at every point of
`D`, `w` is differentiable and `w'` has derivative `r - f w' - g w`. Intended for open `D`. -/
@[dlmf 1.13.E1, dlmf 1.13.E8]
def IsLinODE2SolOn (f g r : 𝕜 → 𝕜) (w : 𝕜 → 𝕜) (D : Set 𝕜) : Prop :=
  ∀ z ∈ D, DifferentiableAt 𝕜 w z ∧
    HasDerivAt (deriv w) (r z - f z * deriv w z - g z * w z) z

/-- DLMF 1.13.2: `w₁`, `w₂` are a **fundamental pair** of the homogeneous equation 1.13.1 on
`D`: both are solutions and every solution is `A w₁ + B w₂` on `D` for constants `A`, `B`. -/
@[dlmf 1.13.E2]
def IsFundamentalPair (f g : 𝕜 → 𝕜) (w₁ w₂ : 𝕜 → 𝕜) (D : Set 𝕜) : Prop :=
  IsLinODE2SolOn f g 0 w₁ D ∧ IsLinODE2SolOn f g 0 w₂ D ∧
    ∀ w, IsLinODE2SolOn f g 0 w D → ∃ A B : 𝕜, ∀ z ∈ D, w z = A * w₁ z + B * w₂ z

/-- DLMF 1.13.4: the **Wronskian** `𝒲{w₁, w₂} = w₁ w₂' - w₂ w₁'`. -/
@[dlmf 1.13.E4]
def wronskian (w₁ w₂ : 𝕜 → 𝕜) (z : 𝕜) : 𝕜 :=
  w₁ z * deriv w₂ z - w₂ z * deriv w₁ z

/-- DLMF §1.13(i): the `n`-argument Wronskian `𝒲{w₁, …, w_n} = det[w_k^{(j-1)}]`, with rows
indexed by the order of the derivative and columns by the function. -/
@[dlmf 1.13.E4]
def wronskianN {n : ℕ} (w : Fin n → 𝕜 → 𝕜) (z : 𝕜) : 𝕜 :=
  (Matrix.of fun (j k : Fin n) => iteratedDeriv j (w k) z).det

/-- DLMF 1.13.20: the **Schwarzian derivative** `{z, ζ} = z'''/z' - (3/2)(z''/z')²` of `z` as a
function of `ζ` (dots in DLMF denote derivatives with respect to `ζ`). -/
@[dlmf 1.13.E20]
def schwarzian (z : 𝕜 → 𝕜) (ζ : 𝕜) : 𝕜 :=
  iteratedDeriv 3 z ζ / deriv z ζ - 3 / 2 * (iteratedDeriv 2 z ζ / deriv z ζ) ^ 2

/-- DLMF 1.13.26: `u` solves the **Sturm–Liouville equation** `(p u')' + (λρ - q) u = 0` on `s`:
`u` is differentiable and `p u'` has derivative `(q - λρ) u` at every point of `s`. -/
@[dlmf 1.13.E26]
def IsSturmLiouvilleSolOn (p q ρ : ℝ → ℝ) (lam : ℝ) (u : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, DifferentiableAt ℝ u x ∧
    HasDerivAt (fun t => p t * deriv u t) ((q x - lam * ρ x) * u x) x

/-- DLMF 1.13.27: the **unmixed boundary conditions** `αu(a) + α'u'(a) = 0`,
`βu(b) + β'u'(b) = 0` (DLMF requires `(α, α') ≠ 0`, `(β, β') ≠ 0`; see
`IsRegularSLEigenvalue`). -/
@[dlmf 1.13.E27]
def SLUnmixedBC (α α' β β' a b : ℝ) (u : ℝ → ℝ) : Prop :=
  α * u a + α' * deriv u a = 0 ∧ β * u b + β' * deriv u b = 0

/-- DLMF 1.13.28: the **periodic boundary conditions** `u(a) = u(b)`, `u'(a) = u'(b)`. -/
@[dlmf 1.13.E28]
def SLPeriodicBC (a b : ℝ) (u : ℝ → ℝ) : Prop :=
  u a = u b ∧ deriv u a = deriv u b

/-- DLMF §1.13(viii): `λ` is an **eigenvalue** of the regular Sturm–Liouville system
1.13.26–1.13.27 on `[a, b]` (`a < b`, `p, ρ > 0` on `[a, b]`, `(α, α') ≠ 0`, `(β, β') ≠ 0`)
if the system has a solution `u` that is not identically zero on `[a, b]`; `u` is then an
eigenfunction. The equation is required on the closed interval (`u` is defined on `ℝ`). -/
@[dlmf 1.13.viii]
def IsRegularSLEigenvalue (p q ρ : ℝ → ℝ) (a b α α' β β' lam : ℝ) : Prop :=
  a < b ∧ (∀ x ∈ Icc a b, 0 < p x ∧ 0 < ρ x) ∧ (α ≠ 0 ∨ α' ≠ 0) ∧ (β ≠ 0 ∨ β' ≠ 0) ∧
    ∃ u : ℝ → ℝ, (∃ x ∈ Icc a b, u x ≠ 0) ∧ IsSturmLiouvilleSolOn p q ρ lam u (Icc a b) ∧
      SLUnmixedBC α α' β β' a b u

/-- DLMF §1.13(viii): `λ` is an eigenvalue of the regular Sturm–Liouville system 1.13.26 with
periodic boundary conditions 1.13.28 on `[a, b]`. -/
@[dlmf 1.13.viii]
def IsPeriodicSLEigenvalue (p q ρ : ℝ → ℝ) (a b lam : ℝ) : Prop :=
  a < b ∧ (∀ x ∈ Icc a b, 0 < p x ∧ 0 < ρ x) ∧
    ∃ u : ℝ → ℝ, (∃ x ∈ Icc a b, u x ≠ 0) ∧ IsSturmLiouvilleSolOn p q ρ lam u (Icc a b) ∧
      SLPeriodicBC a b u

end DLMF.AlgebraicAnalytic
