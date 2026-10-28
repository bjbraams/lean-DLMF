/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Calculus of one and several variables, vector calculus: definitions (DLMF §§1.4–1.7)

This file holds the definitions of DLMF §§1.4–1.6 that have no Mathlib counterpart (namespace
`DLMF.AlgebraicAnalytic`). Everything else (monotonicity, continuity, derivatives, `C^n`,
convexity, total variation `eVariationOn`, `Lᵖ` spaces, the cross and dot products) is
Mathlib's; see `DLMF.AlgebraicAnalytic.Calculus.MathlibCoverage`.

* `IsSimpleDiscontinuity`, `IsPiecewiseContinuousOn` (§1.4(ii)) and the two-variable
  `IsPiecewiseContinuousOnProd` (§1.5(i)).
* `HasCauchyPrincipalValue`, `HasPrincipalValueAtInfinity` (1.4.24, 1.4.25).
* Partial derivatives `partialDeriv i f x` on `Fin n → ℝ`, defined as DLMF does (1.5.3) by the
  derivative of the section `t ↦ f (update x i t)`, so they exist without total
  differentiability; Jacobian determinants `jacobianDet2`, `jacobianDet3` (1.5.38, 1.5.40).
* Cylindrical and spherical coordinates `cylindricalCoord`, `sphericalCoord` (1.5.14, 1.5.16).
* Vector calculus in `ℝ³ = Fin 3 → ℝ`: the magnitude `vecNorm` (1.6.3), the Levi-Civita symbol
  `leviCivita` (1.6.14), `grad`, `divergence`, `curl`, `laplacian`, `vectorLaplacian`
  (1.6.19–1.6.22, 1.6.30, 1.6.34).
* Paths: `pathLength`, `pathIntegral`, `lineIntegral` (1.6.35–1.6.38), `IsSimpleClosedPath`.
* Parametrized surfaces `Φ : ℝ × ℝ → (Fin 3 → ℝ)`: `tangentU`, `tangentV` (1.6.46–1.6.47),
  `IsSmoothSurfaceAt`, `surfaceArea`, `surfaceIntegral`, `fluxIntegral` (1.6.48, 1.6.54,
  1.6.55), and `HasPiecewiseSmoothBoundary`, the hypotheses of Gauss's theorem 1.6.58.

The type `Fin 3 → ℝ` carries the sup norm in Mathlib, so every Euclidean length in §1.6 is
written with `vecNorm a = √(a ⬝ᵥ a)` (DLMF 1.6.3), never with `‖·‖`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology Matrix

namespace DLMF.AlgebraicAnalytic

/-! ### §1.4(ii) Continuity -/

/-- DLMF §1.4(ii): `f` has a simple discontinuity at `c` when both one-sided limits
`f(c+)`, `f(c-)` exist and differ. -/
@[dlmf 1.4.ii]
def IsSimpleDiscontinuity (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ l r : ℝ, Tendsto f (𝓝[<] c) (𝓝 l) ∧ Tendsto f (𝓝[>] c) (𝓝 r) ∧ l ≠ r

/-- DLMF §1.4(ii): `f` is piecewise (sectionally) continuous on the interval `I` if it is
continuous on `I` save for finitely many points of `I`, at each of which both one-sided limits
(within `I`) exist. This allows simple discontinuities and removable singularities. -/
@[dlmf 1.4.ii]
def IsPiecewiseContinuousOn (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ s : Finset ℝ, (∀ x ∈ I, x ∉ s → ContinuousWithinAt f I x) ∧
    ∀ c ∈ s, c ∈ I →
      (∃ l, Tendsto f (𝓝[I ∩ Iio c] c) (𝓝 l)) ∧ ∃ r, Tendsto f (𝓝[I ∩ Ioi c] c) (𝓝 r)

/-- DLMF §1.5(i): `f(x, y)` is piecewise continuous on `I₁ × I₂` if it is piecewise continuous
in `x` for each `y ∈ I₂` and piecewise continuous in `y` for each `x ∈ I₁`. -/
@[dlmf 1.5.i]
def IsPiecewiseContinuousOnProd (f : ℝ × ℝ → ℝ) (I₁ I₂ : Set ℝ) : Prop :=
  (∀ y ∈ I₂, IsPiecewiseContinuousOn (fun x => f (x, y)) I₁) ∧
    ∀ x ∈ I₁, IsPiecewiseContinuousOn (fun y => f (x, y)) I₂

/-! ### §1.4(v) Cauchy principal values -/

/-- DLMF 1.4.24: the Cauchy principal value of `∫ₐᵇ f` at the interior point `c ∈ (a, b)`
is `v`: the integrals over `[a, c - ε]` and `[c + ε, b]` exist for
`0 < ε < min (c - a) (b - c)`, and their sum tends to `v` as `ε → 0+`. -/
@[dlmf 1.4.E24]
def HasCauchyPrincipalValue (f : ℝ → ℂ) (a b c : ℝ) (v : ℂ) : Prop :=
  a < c ∧ c < b ∧
    (∀ ε, 0 < ε → ε < min (c - a) (b - c) →
      IntervalIntegrable f volume a (c - ε) ∧ IntervalIntegrable f volume (c + ε) b) ∧
    Tendsto (fun ε : ℝ => (∫ x in a..c - ε, f x) + ∫ x in c + ε..b, f x) (𝓝[>] 0) (𝓝 v)

/-- DLMF 1.4.25: the principal value of `∫_{-∞}^{∞} f` is `v`: `∫_{-b}^{b} f` exists for every
`b > 0` and tends to `v` as `b → ∞`. -/
@[dlmf 1.4.E25]
def HasPrincipalValueAtInfinity (f : ℝ → ℂ) (v : ℂ) : Prop :=
  (∀ b, 0 < b → IntervalIntegrable f volume (-b) b) ∧
    Tendsto (fun b : ℝ => ∫ x in -b..b, f x) atTop (𝓝 v)

/-! ### §1.5 Partial derivatives, coordinates, Jacobians -/

/-- DLMF 1.5.3–1.5.4: the partial derivative `∂f/∂xᵢ` at `x`, the derivative of the section
`t ↦ f (x₁, …, t, …, xₙ)` at `t = xᵢ` (zero when this derivative does not exist). -/
@[dlmf 1.5.E3, dlmf 1.5.E4]
def partialDeriv {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (i : Fin n)
    (f : (Fin n → ℝ) → E) (x : Fin n → ℝ) : E :=
  deriv (fun t => f (Function.update x i t)) (x i)

/-- DLMF 1.5.38: the Jacobian `∂(f, g)/∂(x, y)` of two functions of `(x, y)`, the determinant
of the matrix of partial derivatives (each one the derivative of a section, 1.5.3–1.5.4). -/
@[dlmf 1.5.E38]
def jacobianDet2 (f g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Matrix.det !![deriv (fun t => f (t, p.2)) p.1, deriv (fun t => f (p.1, t)) p.2;
    deriv (fun t => g (t, p.2)) p.1, deriv (fun t => g (p.1, t)) p.2]

/-- DLMF 1.5.40: the Jacobian `∂(f, g, h)/∂(x, y, z)` of three functions of `(x, y, z)`, the
determinant of the matrix of partial derivatives. -/
@[dlmf 1.5.E40]
def jacobianDet3 (f g h : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  Matrix.det (Matrix.of ![fun j => partialDeriv j f x, fun j => partialDeriv j g x,
    fun j => partialDeriv j h x])

/-- DLMF 1.5.14: cylindrical coordinates, `(r, φ, z) ↦ (r cos φ, r sin φ, z)`. The DLMF ranges
`0 ≤ r`, `0 ≤ φ ≤ 2π` are not imposed on the map. -/
@[dlmf 1.5.E14]
def cylindricalCoord (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2]

/-- DLMF 1.5.16: spherical coordinates (physicists' convention), `(ρ, θ, φ) ↦
(ρ sin θ cos φ, ρ sin θ sin φ, ρ cos θ)`; `θ` is the polar and `φ` the azimuthal angle. The
DLMF ranges `0 ≤ ρ`, `0 ≤ θ ≤ π`, `0 ≤ φ ≤ 2π` are not imposed on the map. -/
@[dlmf 1.5.E16]
def sphericalCoord (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![q 0 * Real.sin (q 1) * Real.cos (q 2), q 0 * Real.sin (q 1) * Real.sin (q 2),
    q 0 * Real.cos (q 1)]

/-! ### §1.6(i)–(ii) Vectors -/

/-- DLMF 1.6.3: the magnitude `‖a‖ = √(a · a)` of a vector of `ℝ³` (the Euclidean norm; the
Mathlib norm on `Fin 3 → ℝ` is the sup norm). -/
@[dlmf 1.6.E3]
def vecNorm (a : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (a ⬝ᵥ a)

/-- DLMF 1.6.14: the Levi-Civita symbol `ε_{jkℓ}` on `{1, 2, 3}` (here `Fin 3`), `+1` for an
even and `-1` for an odd permutation of `(1, 2, 3)` and `0` otherwise. It is given by the
closed formula `(j - k)(k - ℓ)(ℓ - j)/2`; `leviCivita_perm` identifies it with the sign. -/
@[dlmf 1.6.E14]
def leviCivita (j k l : Fin 3) : ℤ :=
  ((j : ℤ) - k) * ((k : ℤ) - l) * ((l : ℤ) - j) / 2

/-! ### §1.6(iii) Vector-valued functions -/

/-- DLMF 1.6.19–1.6.20: the gradient `∇f = (∂f/∂x, ∂f/∂y, ∂f/∂z)` of a scalar function on
`ℝ³`. -/
@[dlmf 1.6.E19, dlmf 1.6.E20]
def grad (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => partialDeriv i f x

/-- DLMF 1.6.21: the divergence `∇ · F = ∂F₁/∂x + ∂F₂/∂y + ∂F₃/∂z`. -/
@[dlmf 1.6.E21]
def divergence (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i, partialDeriv i (fun y => F y i) x

/-- DLMF 1.6.22: the curl `∇ × F = (∂F₃/∂y - ∂F₂/∂z, ∂F₁/∂z - ∂F₃/∂x, ∂F₂/∂x - ∂F₁/∂y)`. -/
@[dlmf 1.6.E22]
def curl (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![partialDeriv 1 (fun y => F y 2) x - partialDeriv 2 (fun y => F y 1) x,
    partialDeriv 2 (fun y => F y 0) x - partialDeriv 0 (fun y => F y 2) x,
    partialDeriv 0 (fun y => F y 1) x - partialDeriv 1 (fun y => F y 0) x]

/-- DLMF 1.6.30 (and 1.5.15): the Laplacian `∇²f = ∂²f/∂x² + ∂²f/∂y² + ∂²f/∂z²`;
`laplacian_eq_div_grad` is 1.6.30, `∇²f = ∇ · (∇f)`. -/
@[dlmf 1.6.E30]
def laplacian (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i, partialDeriv i (fun y => partialDeriv i f y) x

/-- DLMF 1.6.34: the vector Laplacian `∇²F`, the Laplacian of each Cartesian component. -/
@[dlmf 1.6.E34]
def vectorLaplacian (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => laplacian (fun y => F y i) x

/-! ### §1.6(iv) Paths and line integrals -/

/-- DLMF 1.6.36: the length `∫ₐᵇ ‖c'(t)‖ dt` of a path `c : ℝ → ℝ³`, with the Euclidean
magnitude `vecNorm` and `c'(t)` the componentwise derivative (1.6.35). -/
@[dlmf 1.6.E35, dlmf 1.6.E36]
def pathLength (c : ℝ → Fin 3 → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, vecNorm (deriv c t)

/-- DLMF 1.6.37: the path integral `∫_c f ds = ∫ₐᵇ f(c(t)) ‖c'(t)‖ dt`. -/
@[dlmf 1.6.E37]
def pathIntegral (f : (Fin 3 → ℝ) → ℝ) (c : ℝ → Fin 3 → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, f (c t) * vecNorm (deriv c t)

/-- DLMF 1.6.38: the line integral `∫_c F · ds = ∫ₐᵇ F(c(t)) · c'(t) dt`. -/
@[dlmf 1.6.E38]
def lineIntegral (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (c : ℝ → Fin 3 → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, F (c t) ⬝ᵥ deriv c t

/-- DLMF §1.6(iv): `c` on `[a, b]` (`a < b`) traces a simple closed curve: `c(a) = c(b)` and
`c` is one-to-one on `[a, b)`. -/
@[dlmf 1.6.iv]
def IsSimpleClosedPath {X : Type*} (c : ℝ → X) (a b : ℝ) : Prop :=
  a < b ∧ c a = c b ∧ InjOn c (Ico a b)

/-! ### §1.6(v) Surfaces -/

/-- DLMF 1.6.46: the tangent vector `T_u = ∂Φ/∂u` of a parametrized surface `Φ(u, v)`
(1.6.45). -/
@[dlmf 1.6.E45, dlmf 1.6.E46]
def tangentU (Φ : ℝ × ℝ → Fin 3 → ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  deriv (fun u => Φ (u, p.2)) p.1

/-- DLMF 1.6.47: the tangent vector `T_v = ∂Φ/∂v` of a parametrized surface `Φ(u, v)`. -/
@[dlmf 1.6.E47]
def tangentV (Φ : ℝ × ℝ → Fin 3 → ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  deriv (fun v => Φ (p.1, v)) p.2

/-- DLMF §1.6(v): the parametrized surface `Φ` is smooth at `p` if `T_u × T_v ≠ 0` there. -/
@[dlmf 1.6.v]
def IsSmoothSurfaceAt (Φ : ℝ × ℝ → Fin 3 → ℝ) (p : ℝ × ℝ) : Prop :=
  tangentU Φ p ⨯₃ tangentV Φ p ≠ 0

/-- DLMF 1.6.48: the area `A(S) = ∬_D ‖T_u × T_v‖ du dv` of the surface `Φ(D)`. -/
@[dlmf 1.6.E48]
def surfaceArea (Φ : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in D, vecNorm (tangentU Φ p ⨯₃ tangentV Φ p)

/-- DLMF 1.6.54: the integral `∬_S f dS = ∬_D f(Φ(u, v)) ‖T_u × T_v‖ du dv`. -/
@[dlmf 1.6.E54]
def surfaceIntegral (f : (Fin 3 → ℝ) → ℝ) (Φ : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in D, f (Φ p) * vecNorm (tangentU Φ p ⨯₃ tangentV Φ p)

/-- DLMF 1.6.55: the flux `∬_S F · dS = ∬_D F(Φ(u, v)) · (T_u × T_v) du dv`. -/
@[dlmf 1.6.E55]
def fluxIntegral (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (Φ : ℝ × ℝ → Fin 3 → ℝ)
    (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in D, F (Φ p) ⬝ᵥ (tangentU Φ p ⨯₃ tangentV Φ p)

/-- DLMF §1.6(v) (hypotheses of Gauss's theorem 1.6.58): `V ⊆ ℝ³` is compact, its boundary
is the union of the closures of finitely many smooth, one-to-one `C¹` patches `Φ i (D i)`
(`D i` open and bounded, with null boundary in the parameter plane), the open patches are
pairwise disjoint, and each normal `T_u × T_v` points out of `V`. This is DLMF's "piecewise
smooth surface which forms the complete boundary of a bounded closed point set `V`, oriented
by its normal being outwards". -/
@[dlmf 1.6.v]
structure HasPiecewiseSmoothBoundary (V : Set (Fin 3 → ℝ)) (ι : Type*) [Fintype ι]
    (Φ : ι → ℝ × ℝ → Fin 3 → ℝ) (D : ι → Set (ℝ × ℝ)) : Prop where
  /-- The region enclosed by the boundary patches is compact. -/
  compact : IsCompact V
  /-- Each boundary patch has an open parameter domain. -/
  isOpen : ∀ i, IsOpen (D i)
  /-- Each boundary patch has a bounded parameter domain. -/
  bounded : ∀ i, Bornology.IsBounded (D i)
  /-- The frontier of each patch parameter domain has zero planar volume. -/
  null_frontier : ∀ i, volume (frontier (D i)) = 0
  /-- Each boundary parametrization is continuously differentiable. -/
  contDiff : ∀ i, ContDiff ℝ 1 (Φ i)
  /-- Each boundary parametrization is injective on its parameter domain. -/
  injOn : ∀ i, InjOn (Φ i) (D i)
  /-- The boundary arcs satisfy the stated smoothness condition. -/
  smooth : ∀ i, ∀ p ∈ D i, IsSmoothSurfaceAt (Φ i) p
  /-- Distinct boundary arcs have disjoint interiors. -/
  disjoint : Pairwise fun i j => Disjoint (Φ i '' D i) (Φ j '' D j)
  /-- The boundary arcs cover the frontier. -/
  cover : frontier V = ⋃ i, Φ i '' closure (D i)
  /-- The chosen normal points outward along the boundary. -/
  outward : ∀ i, ∀ p ∈ D i, ∀ᶠ t in 𝓝[>] (0 : ℝ),
    Φ i p + t • (tangentU (Φ i) p ⨯₃ tangentV (Φ i) p) ∉ V ∧
      Φ i p - t • (tangentU (Φ i) p ⨯₃ tangentV (Φ i) p) ∈ interior V

end DLMF.AlgebraicAnalytic
