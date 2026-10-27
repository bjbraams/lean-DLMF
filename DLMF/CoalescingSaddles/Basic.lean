/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Integrals with coalescing saddles: definitions (DLMF Chapter 36)

This file holds the definitions of DLMF Chapter 36 (namespace `DLMF.CoalescingSaddles`).

## Potentials (DLMF 36.2.1–36.2.3)

* `cuspoidPotential K t x = t^(K+2) + ∑ₘ xₘ t^m` (36.2.1), for complex `t` and real
  parameters `x : Fin K → ℝ`; the coefficient of `t^(m+1)` is `x m`, so DLMF's `x₁, x₂, …`
  are `x 0, x 1, …`. `K = 1, 2, 3` are the fold, cusp and swallowtail.
* `ellipticUmbilicPotential s t x y z` (36.2.2), `hyperbolicUmbilicPotential s t x y z`
  (36.2.3), for complex `s, t` and real `x, y, z`.

## Canonical integrals (DLMF 36.2.4, 36.2.5, 36.2.10, 36.2.11)

The integrals `∫ exp(iΦ)` of DLMF over `ℝ` or `ℝ²` are oscillatory and not absolutely
convergent. Following the DLMF remark in §36.2(i) ("the convergence … can be confirmed by
rotating the integration paths in the complex plane"), they are defined here as absolutely
convergent Bochner integrals over rotated contours; the agreement with the improper real
integrals of DLMF is stated separately (`DLMF.CoalescingSaddles.CanonicalIntegrals`).

* Cuspoids: with `n = K + 2` and `θ = π/(2n)`, the contour is `r ↦ r·d(r)` for `r ∈ ℝ`, where
  `d(r) = e^{iθ}` for `r ≥ 0` and, for `r < 0`, `d(r) = e^{iθ}` if `K` is even (a straight line)
  and `e^{-iθ}` if `K` is odd (a V through `0`). On both rays `(r d(r))ⁿ = i|r|ⁿ`, so
  `|exp(iΦ_K)| = exp(-|r|ⁿ + O(|r|^{n-1}))`. `cuspoidIntegral K x = ∫ d(r) exp(iΦ_K(r d(r); x)) dr`.
* Hyperbolic umbilic: the product of two cubic V-contours (`K = 1`) in `s` and in `t`.
* Elliptic umbilic: with `a = s + it`, `b = s - it` the cubic part is `(a³ + b³)/2`; the real
  `(s, t)`-plane is replaced by the 2-cycle `∑ ε_{jk} ρ_j × ρ_k` of products of the rays
  `ρ_j = e^{i(π/6 + 2πj/3)}·[0, ∞)` in the `a`- and `b`-planes, with the integer matrix
  `ε = [[-1,0,1],[0,1,-1],[1,-1,0]]` (`ellipticUmbilicCycle`) and Jacobian `ds dt = (i/2) da db`.
  This choice was checked numerically against 36.2.6, 36.2.7, 36.2.18, 36.2.20, 36.2.24–36.2.26
  and 36.2.28 at sample points (agreement to 12 digits).
* Diffraction catastrophes `Ψ(x; k)` (36.2.10, 36.2.11) use the same contours with phase `kΦ`;
  DLMF requires `k > 0`.

## Critical points, bifurcation sets and Stokes sets (§§36.4, 36.5)

Derivatives are complex derivatives of the polynomial potentials (`deriv`, `iteratedDeriv`), and
real critical points are real arguments at which they vanish. Stokes sets are formalized by the
exponential dominance condition 36.5.1 together with a connecting path on which `Re Φ` is constant
(DLMF's steepest-descent path).

## Scaling exponents (§36.6)

`cuspoidSingularityIndex` (`β_K`), `cuspoidCoordinateIndex` (`γ_{mK}`), `cuspoidVolumeIndex`
(`γ_K`), and the umbilic exponents.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace DLMF.CoalescingSaddles

/-! ### Potentials -/

/-- The cuspoid catastrophe of codimension `K` (DLMF 36.2.1):
`Φ_K(t; x) = t^{K+2} + ∑_{m=1}^K x_m t^m`. The argument `t` is complex and the parameters are
real; `x m` is DLMF's `x_{m+1}`, the coefficient of `t^{m+1}`. -/
@[dlmf 36.2.E1]
def cuspoidPotential (K : ℕ) (t : ℂ) (x : Fin K → ℝ) : ℂ :=
  t ^ (K + 2) + ∑ m : Fin K, ((x m : ℝ) : ℂ) * t ^ ((m : ℕ) + 1)

/-- The elliptic umbilic catastrophe (DLMF 36.2.2):
`Φ^{(E)}(s, t; x, y, z) = s³ - 3st² + z(s² + t²) + yt + xs`, for complex `s, t` and real
parameters `x, y, z`. -/
@[dlmf 36.2.E2]
def ellipticUmbilicPotential (s t : ℂ) (x y z : ℝ) : ℂ :=
  s ^ 3 - 3 * s * t ^ 2 + (z : ℂ) * (s ^ 2 + t ^ 2) + (y : ℂ) * t + (x : ℂ) * s

/-- The hyperbolic umbilic catastrophe (DLMF 36.2.3):
`Φ^{(H)}(s, t; x, y, z) = s³ + t³ + zst + yt + xs`, for complex `s, t` and real
parameters `x, y, z`. -/
@[dlmf 36.2.E3]
def hyperbolicUmbilicPotential (s t : ℂ) (x y z : ℝ) : ℂ :=
  s ^ 3 + t ^ 3 + (z : ℂ) * s * t + (y : ℂ) * t + (x : ℂ) * s

/-! ### Contours -/

/-- The rotation angle `π/(2(K+2))` of the cuspoid contour: on the ray `t = r e^{iθ}`,
`i t^{K+2} = -r^{K+2}`. -/
def cuspoidAngle (K : ℕ) : ℝ := π / (2 * ((K : ℝ) + 2))

/-- The direction `d(r)` of the rotated cuspoid contour `r ↦ r d(r)`, `r ∈ ℝ`: `e^{iθ}` for
`r ≥ 0`; for `r < 0`, `e^{iθ}` when `K` is even and `e^{-iθ}` when `K` is odd, with
`θ = cuspoidAngle K`. The contour runs from `∞·e^{i(π+θ)}` (`K` even) or `∞·e^{i(π-θ)}`
(`K` odd) to `∞·e^{iθ}`; both ends lie in sectors where `exp(i t^{K+2})` decays. -/
def cuspoidContourDir (K : ℕ) (r : ℝ) : ℂ :=
  if 0 ≤ r ∨ Even K then exp ((cuspoidAngle K : ℂ) * I) else exp (-(cuspoidAngle K : ℂ) * I)

/-- The rotated cuspoid contour `r ↦ r d(r)` (see `cuspoidContourDir`). -/
def cuspoidContour (K : ℕ) (r : ℝ) : ℂ := (r : ℂ) * cuspoidContourDir K r

/-- The direction `e^{i(π/6 + 2πj/3)}` (`j = 0, 1, 2`: angles `π/6`, `5π/6`, `3π/2`) of the rays
on which `exp(i a³/2)` decays; used for the elliptic umbilic cycle. -/
def ellipticUmbilicRayDir (j : Fin 3) : ℂ :=
  exp (((π / 6 + 2 * π * (j : ℕ) / 3 : ℝ) : ℂ) * I)

/-- The coefficients `ε_{jk}` of the 2-cycle `∑ ε_{jk} ρ_j × ρ_k` that replaces the real
`(s, t)`-plane in the elliptic umbilic integral (rows and columns sum to zero, so it is a cycle
relative to the decay region). -/
def ellipticUmbilicCycle (j k : Fin 3) : ℤ :=
  !![-1, 0, 1; 0, 1, -1; 1, -1, 0] j k

/-- The elliptic umbilic potential in the coordinates `a = s + it`, `b = s - it`, that is at
`s = (a + b)/2`, `t = (a - b)/(2i)`; its cubic part is `(a³ + b³)/2`. -/
def ellipticUmbilicPotentialAB (a b : ℂ) (x y z : ℝ) : ℂ :=
  ellipticUmbilicPotential ((a + b) / 2) ((a - b) / (2 * I)) x y z

/-! ### Canonical integrals and diffraction catastrophes -/

/-- The cuspoid canonical integral `Ψ_K(x) = ∫_{-∞}^{∞} exp(iΦ_K(t; x)) dt` (DLMF 36.2.4), defined
as the absolutely convergent integral over the rotated contour `t = r d(r)` (see
`cuspoidContourDir`); the improper real integral of DLMF converges to it
(`hasIntegralWholeLine_cuspoidIntegral`). Real parameters `x`. -/
@[dlmf 36.2.E4]
def cuspoidIntegral (K : ℕ) (x : Fin K → ℝ) : ℂ :=
  ∫ r : ℝ, cuspoidContourDir K r * exp (I * cuspoidPotential K (cuspoidContour K r) x)

/-- The hyperbolic umbilic canonical integral
`Ψ^{(H)}(x) = ∫∫ exp(iΦ^{(H)}(s, t; x)) ds dt` (DLMF 36.2.5, `U = H`), defined as the absolutely
convergent integral over the product of the cubic V-contours `s = σ d(σ)`, `t = τ d(τ)`
(`K = 1`: rays at angles `π/6` and `5π/6`). Real parameters `x, y, z`. -/
@[dlmf 36.2.E5]
def hyperbolicUmbilicIntegral (x y z : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ, cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
    exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y z)

/-- The integral of the 2-form `exp(iκΦ^{(E)}) da db` over the product of the rays `ρ_j × ρ_k`
(`a = r e_j`, `b = q e_k`, `r, q > 0`). -/
def ellipticUmbilicQuadrant (κ : ℝ) (x y z : ℝ) (j k : Fin 3) : ℂ :=
  ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioi 0, ellipticUmbilicRayDir j * ellipticUmbilicRayDir k *
    exp (I * (κ : ℂ) * ellipticUmbilicPotentialAB ((p.1 : ℂ) * ellipticUmbilicRayDir j)
      ((p.2 : ℂ) * ellipticUmbilicRayDir k) x y z)

/-- The elliptic umbilic canonical integral
`Ψ^{(E)}(x) = ∫∫ exp(iΦ^{(E)}(s, t; x)) ds dt` (DLMF 36.2.5, `U = E`), defined as the absolutely
convergent integral `(i/2) ∑ ε_{jk} ∫_{ρ_j × ρ_k} exp(iΦ^{(E)}) da db` over the cycle
`ellipticUmbilicCycle` in the coordinates `a = s + it`, `b = s - it`. Real parameters. -/
@[dlmf 36.2.E5]
def ellipticUmbilicIntegral (x y z : ℝ) : ℂ :=
  I / 2 * ∑ j : Fin 3, ∑ k : Fin 3,
    (ellipticUmbilicCycle j k : ℂ) * ellipticUmbilicQuadrant 1 x y z j k

/-- The cuspoid diffraction catastrophe `Ψ_K(x; k) = √k ∫ exp(ikΦ_K(t; x)) dt` (DLMF 36.2.10),
over the rotated contour of `cuspoidIntegral`. DLMF: `k > 0` (for `k ≤ 0` the value is
not meaningful). -/
@[dlmf 36.2.E10]
def cuspoidDiffraction (K : ℕ) (x : Fin K → ℝ) (k : ℝ) : ℂ :=
  (Real.sqrt k : ℂ) *
    ∫ r : ℝ, cuspoidContourDir K r * exp (I * (k : ℂ) * cuspoidPotential K (cuspoidContour K r) x)

/-- The hyperbolic umbilic diffraction catastrophe `Ψ^{(H)}(x; k) = k ∫∫ exp(ikΦ^{(H)}) ds dt`
(DLMF 36.2.11, `U = H`), over the contour of `hyperbolicUmbilicIntegral`; DLMF: `k > 0`. -/
@[dlmf 36.2.E11]
def hyperbolicUmbilicDiffraction (x y z k : ℝ) : ℂ :=
  (k : ℂ) * ∫ p : ℝ × ℝ, cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
    exp (I * (k : ℂ) *
      hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y z)

/-- The elliptic umbilic diffraction catastrophe `Ψ^{(E)}(x; k) = k ∫∫ exp(ikΦ^{(E)}) ds dt`
(DLMF 36.2.11, `U = E`), over the cycle of `ellipticUmbilicIntegral`; DLMF: `k > 0`. -/
@[dlmf 36.2.E11]
def ellipticUmbilicDiffraction (x y z k : ℝ) : ℂ :=
  (k : ℂ) * (I / 2 * ∑ j : Fin 3, ∑ l : Fin 3,
    (ellipticUmbilicCycle j l : ℂ) * ellipticUmbilicQuadrant k x y z j l)

/-- The Pearcey integral `P(x₂, x₁) = Ψ₂(x₁, x₂)` (DLMF 36.2.14); note the order of the
arguments. -/
@[dlmf 36.2.E14]
def pearcey (x₂ x₁ : ℝ) : ℂ := cuspoidIntegral 2 ![x₁, x₂]

/-! ### Critical points and bifurcation sets (§36.4) -/

/-- The real critical points `t_j(x)` of the cuspoid potential (DLMF 36.4.1):
real `t` with `∂Φ_K/∂t (t; x) = 0`. -/
@[dlmf 36.4.E1]
def cuspoidCriticalPoints (K : ℕ) (x : Fin K → ℝ) : Set ℝ :=
  {t | deriv (fun u => cuspoidPotential K u x) (t : ℂ) = 0}

/-- The bifurcation (catastrophe) set of the cuspoid of codimension `K` (DLMF 36.4.3): the
parameters `x` at which a real critical point is degenerate, `∂Φ/∂t = ∂²Φ/∂t² = 0`. -/
@[dlmf 36.4.E3]
def cuspoidBifurcationSet (K : ℕ) : Set (Fin K → ℝ) :=
  {x | ∃ t : ℝ, deriv (fun u => cuspoidPotential K u x) (t : ℂ) = 0 ∧
    iteratedDeriv 2 (fun u => cuspoidPotential K u x) (t : ℂ) = 0}

/-- The cusp lines (ribs) of a cuspoid bifurcation set (DLMF 36.4.9 for the swallowtail): the
parameters at which three real critical points coalesce, `∂Φ/∂t = ∂²Φ/∂t² = ∂³Φ/∂t³ = 0`. -/
def cuspoidCuspLines (K : ℕ) : Set (Fin K → ℝ) :=
  {x | ∃ t : ℝ, deriv (fun u => cuspoidPotential K u x) (t : ℂ) = 0 ∧
    iteratedDeriv 2 (fun u => cuspoidPotential K u x) (t : ℂ) = 0 ∧
    iteratedDeriv 3 (fun u => cuspoidPotential K u x) (t : ℂ) = 0}

/-- The self-intersection set of a cuspoid bifurcation set (DLMF 36.4.8 for the swallowtail):
the parameters at which two distinct real critical points are both degenerate. -/
def cuspoidSelfIntersection (K : ℕ) : Set (Fin K → ℝ) :=
  {x | ∃ t₁ t₂ : ℝ, t₁ ≠ t₂ ∧
    deriv (fun u => cuspoidPotential K u x) (t₁ : ℂ) = 0 ∧
    iteratedDeriv 2 (fun u => cuspoidPotential K u x) (t₁ : ℂ) = 0 ∧
    deriv (fun u => cuspoidPotential K u x) (t₂ : ℂ) = 0 ∧
    iteratedDeriv 2 (fun u => cuspoidPotential K u x) (t₂ : ℂ) = 0}

/-- `(s, t)` is a (complex) critical point of the two-variable function `P`:
`∂P/∂s = ∂P/∂t = 0` (DLMF 36.4.2). -/
def IsCriticalPoint₂ (P : ℂ → ℂ → ℂ) (s t : ℂ) : Prop :=
  deriv (fun u => P u t) s = 0 ∧ deriv (fun u => P s u) t = 0

/-- The Hessian determinant `P_ss P_tt - P_st²` of a two-variable function (DLMF 36.4.4). -/
def hessianDet₂ (P : ℂ → ℂ → ℂ) (s t : ℂ) : ℂ :=
  deriv (fun u => deriv (fun v => P v t) u) s * deriv (fun u => deriv (fun v => P s v) u) t -
    deriv (fun u => deriv (fun v => P u v) t) s ^ 2

/-- The real critical points `(s_j(x), t_j(x))` of an umbilic potential (DLMF 36.4.2);
`Φ` is `ellipticUmbilicPotential` or `hyperbolicUmbilicPotential`. -/
@[dlmf 36.4.E2]
def umbilicCriticalPoints (Φ : ℂ → ℂ → ℝ → ℝ → ℝ → ℂ) (x y z : ℝ) : Set (ℝ × ℝ) :=
  {p | IsCriticalPoint₂ (fun s t => Φ s t x y z) p.1 p.2}

/-- The bifurcation set of an umbilic catastrophe (DLMF 36.4.4): the parameters `(x, y, z)` at
which a real critical point has vanishing Hessian determinant. -/
@[dlmf 36.4.E4]
def umbilicBifurcationSet (Φ : ℂ → ℂ → ℝ → ℝ → ℝ → ℂ) : Set (ℝ × ℝ × ℝ) :=
  {p | ∃ s t : ℝ, IsCriticalPoint₂ (fun s t => Φ s t p.1 p.2.1 p.2.2) s t ∧
    hessianDet₂ (fun s t => Φ s t p.1 p.2.1 p.2.2) s t = 0}

/-- The cusp lines (ribs) of an umbilic bifurcation set (DLMF 36.4.11, 36.4.13): parameters at
which a real critical point `(s, t)` is a cusp point, i.e. there is a real direction `(u, v) ≠ 0`
in the kernel of the Hessian along which the third derivative also vanishes. With
`g(λ) = Φ(s + λu, t + λv)`, the kernel condition is that `λ ↦ ∂Φ/∂s, ∂Φ/∂t` along the line have
zero derivative at `λ = 0`, and the cusp condition is `g'''(0) = 0`. -/
def umbilicCuspLines (Φ : ℂ → ℂ → ℝ → ℝ → ℝ → ℂ) : Set (ℝ × ℝ × ℝ) :=
  {p | ∃ s t u v : ℝ, (u, v) ≠ (0, 0) ∧
    IsCriticalPoint₂ (fun s t => Φ s t p.1 p.2.1 p.2.2) s t ∧
    deriv (fun l : ℂ => deriv (fun w => Φ w (t + l * v) p.1 p.2.1 p.2.2) (s + l * u)) 0 = 0 ∧
    deriv (fun l : ℂ => deriv (fun w => Φ (s + l * u) w p.1 p.2.1 p.2.2) (t + l * v)) 0 = 0 ∧
    iteratedDeriv 3 (fun l : ℂ => Φ (s + l * u) (t + l * v) p.1 p.2.1 p.2.2) 0 = 0}

/-! ### Stokes sets (§36.5) -/

/-- Two distinct critical points `t₁ ≠ t₂` of the one-variable function `f` are connected by a
path on which `Re f` is constant (DLMF's steepest-descent path for `exp(ikf)`); in particular
`Re (f t₁ - f t₂) = 0`, the exponential dominance condition 36.5.1. -/
def IsSaddleConnection (f : ℂ → ℂ) (t₁ t₂ : ℂ) : Prop :=
  deriv f t₁ = 0 ∧ deriv f t₂ = 0 ∧ t₁ ≠ t₂ ∧
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) ∧ γ 0 = t₁ ∧ γ 1 = t₂ ∧
      ∀ u ∈ Icc (0 : ℝ) 1, (f (γ u)).re = (f t₁).re

/-- Two distinct critical points of the two-variable function `P` connected by a path in `ℂ²` on
which `Re P` is constant (DLMF 36.5.1, umbilics). -/
def IsSaddleConnection₂ (P : ℂ → ℂ → ℂ) (p q : ℂ × ℂ) : Prop :=
  IsCriticalPoint₂ P p.1 p.2 ∧ IsCriticalPoint₂ P q.1 q.2 ∧ p ≠ q ∧
    ∃ γ : ℝ → ℂ × ℂ, ContinuousOn γ (Icc 0 1) ∧ γ 0 = p ∧ γ 1 = q ∧
      ∀ u ∈ Icc (0 : ℝ) 1, (P (γ u).1 (γ u).2).re = (P p.1 p.2).re

/-- The Stokes set of the cuspoid of codimension `K` (DLMF 36.5.1, §36.5(i)): parameters `x` at
which a real critical point `t_j` is connected to a critical point `t_μ` with nonreal value by a
path of constant `Re Φ_K`. -/
@[dlmf 36.5.E1]
def cuspoidStokesSet (K : ℕ) : Set (Fin K → ℝ) :=
  {x | ∃ (t : ℝ) (μ : ℂ), μ.im ≠ 0 ∧ IsSaddleConnection (fun u => cuspoidPotential K u x) t μ}

/-- The part of the cuspoid Stokes surface that connects two complex critical points (DLMF
§36.5(i): "unless stated otherwise"; used in 36.5.10). Complex conjugate pairs, which always have
equal `Re Φ` for real `x`, are excluded. -/
def cuspoidComplexStokesSet (K : ℕ) : Set (Fin K → ℝ) :=
  {x | ∃ μ ν : ℂ, μ.im ≠ 0 ∧ ν.im ≠ 0 ∧ ν ≠ (starRingEnd ℂ) μ ∧
    IsSaddleConnection (fun u => cuspoidPotential K u x) μ ν}

/-- The Stokes set of an umbilic catastrophe (DLMF 36.5.1): a real critical point connected to a
nonreal critical point by a path of constant `Re Φ`. -/
@[dlmf 36.5.E1]
def umbilicStokesSet (Φ : ℂ → ℂ → ℝ → ℝ → ℝ → ℂ) : Set (ℝ × ℝ × ℝ) :=
  {p | ∃ (s t : ℝ) (q : ℂ × ℂ), (q.1.im ≠ 0 ∨ q.2.im ≠ 0) ∧
    IsSaddleConnection₂ (fun s t => Φ s t p.1 p.2.1 p.2.2) ((s : ℂ), (t : ℂ)) q}

/-- The part of an umbilic Stokes surface connecting two nonreal critical points that are not
complex conjugates of each other (used in 36.5.18). -/
def umbilicComplexStokesSet (Φ : ℂ → ℂ → ℝ → ℝ → ℝ → ℂ) : Set (ℝ × ℝ × ℝ) :=
  {p | ∃ q r : ℂ × ℂ, (q.1.im ≠ 0 ∨ q.2.im ≠ 0) ∧ (r.1.im ≠ 0 ∨ r.2.im ≠ 0) ∧
    r ≠ ((starRingEnd ℂ) q.1, (starRingEnd ℂ) q.2) ∧
    IsSaddleConnection₂ (fun s t => Φ s t p.1 p.2.1 p.2.2) q r}

/-! ### Parametrizations of Stokes sets (§36.5) -/

/-- The quintic `80ξ⁵ - 40ξ⁴ - 55ξ³ + 5ξ² + 20ξ - 1` whose two smallest positive roots `x_±`
determine the swallowtail Stokes set at `z = 0` (DLMF 36.5.4). -/
@[dlmf 36.5.E4]
def swallowtailStokesQuintic (ξ : ℝ) : ℝ :=
  80 * ξ ^ 5 - 40 * ξ ^ 4 - 55 * ξ ^ 3 + 5 * ξ ^ 2 + 20 * ξ - 1

/-- The coefficient `B = 10^{-1/3}(2ξ^{4/3} - ξ^{-2/3}/2)` of the swallowtail Stokes curves
`x = B|y|^{4/3}` at `z = 0`, evaluated at a root `ξ = x_±` of 36.5.4 (DLMF 36.5.3). -/
@[dlmf 36.5.E3]
def swallowtailStokesB (ξ : ℝ) : ℝ :=
  (10 : ℝ) ^ (-(1 : ℝ) / 3) * (2 * ξ ^ ((4 : ℝ) / 3) - 1 / 2 * ξ ^ (-(2 : ℝ) / 3))

/-- The auxiliary quantity `t = -u + (|Y|/(10u) - u² - (3/10) σ)^{1/2}` of the swallowtail Stokes
set for `z ≠ 0`, with `σ = sign z` (DLMF 36.5.9). -/
@[dlmf 36.5.E9]
def swallowtailStokesT (u Y σ : ℝ) : ℝ :=
  -u + Real.sqrt (|Y| / (10 * u) - u ^ 2 - 3 / 10 * σ)

/-- The scaled coordinate `X = 9/20 + 20u⁴ - Y²/(20u²) + 6u² σ` of the swallowtail Stokes set,
with `σ = sign z` (DLMF 36.5.7). -/
@[dlmf 36.5.E7]
def swallowtailStokesX (u Y σ : ℝ) : ℝ :=
  9 / 20 + 20 * u ^ 4 - Y ^ 2 / (20 * u ^ 2) + 6 * u ^ 2 * σ

/-- The left side of the swallowtail Stokes equation (DLMF 36.5.8), with `σ = sign z` and
`t = swallowtailStokesT u Y σ`:
`16u⁵ - Y²/(10u) + 4u³σ - (3/10)|Y|σ + 4t⁵ + 2t³σ + |Y|t²`. -/
@[dlmf 36.5.E8]
def swallowtailStokesEq (u Y σ : ℝ) : ℝ :=
  let t := swallowtailStokesT u Y σ
  16 * u ^ 5 - Y ^ 2 / (10 * u) + 4 * u ^ 3 * σ - 3 / 10 * |Y| * σ + 4 * t ^ 5 +
    2 * t ^ 3 * σ + |Y| * t ^ 2

/-- The auxiliary quantity of the elliptic umbilic Stokes set (DLMF 36.5.13), with
`η = y/z²`: `w = u - 2/3 + ((2/3 - u)² + |η/6| ((2/3 - u)/u)^{1/2})^{1/2}`. -/
@[dlmf 36.5.E13]
def ellipticStokesW (u η : ℝ) : ℝ :=
  u - 2 / 3 + Real.sqrt ((2 / 3 - u) ^ 2 + |η / 6| * Real.sqrt ((2 / 3 - u) / u))

/-- The function `Y(u, X) = 8u - 24u² + X(u - 1/6)/(u(u - 1/3))^{1/2}` of the hyperbolic umbilic
Stokes set (DLMF 36.5.16). -/
@[dlmf 36.5.E16]
def hyperbolicStokesY (u X : ℝ) : ℝ :=
  8 * u - 24 * u ^ 2 + X * (u - 1 / 6) / Real.sqrt (u * (u - 1 / 3))

/-- The function `f(u, X) = 16u³ - 4u² - |X|(u/(u - 1/3))^{1/2}/6` of the hyperbolic umbilic
Stokes set (DLMF 36.5.16). -/
@[dlmf 36.5.E16]
def hyperbolicStokesF (u X : ℝ) : ℝ :=
  16 * u ^ 3 - 4 * u ^ 2 - 1 / 6 * |X| * Real.sqrt (u / (u - 1 / 3))

/-- The auxiliary quantity
`w = (1/3 + u)(1 - (1 - |X|/(12u^{1/2}(1/3 + u)^{3/2}))^{1/2})` of the hyperbolic umbilic Stokes
set (DLMF 36.5.21). -/
@[dlmf 36.5.E21]
def hyperbolicStokesW (u X : ℝ) : ℝ :=
  (1 / 3 + u) *
    (1 - Real.sqrt (1 - |X| / (12 * Real.sqrt u * (1 / 3 + u) ^ ((3 : ℝ) / 2))))

/-! ### Scaling exponents (§36.6) -/

/-- The cuspoid singularity index `β_K = K/(2(K+2))` (DLMF 36.6.3). -/
@[dlmf 36.6.E3]
def cuspoidSingularityIndex (K : ℕ) : ℝ := K / (2 * ((K : ℝ) + 2))

/-- The umbilic singularity index `β^{(U)} = 1/3` (DLMF 36.6.3). -/
@[dlmf 36.6.E3]
def umbilicSingularityIndex : ℝ := 1 / 3

/-- The cuspoid coordinate scaling index `γ_{mK} = 1 - m/(K+2)` (DLMF 36.6.4), for `m = 1, …, K`
(as a function of the natural number `m`). -/
@[dlmf 36.6.E4]
def cuspoidCoordinateIndex (m K : ℕ) : ℝ := 1 - m / ((K : ℝ) + 2)

/-- The umbilic coordinate scaling indices `(γ_x, γ_y, γ_z) = (2/3, 2/3, 1/3)` (DLMF 36.6.4). -/
@[dlmf 36.6.E4]
def umbilicCoordinateIndex : Fin 3 → ℝ := ![2 / 3, 2 / 3, 1 / 3]

/-- The cuspoid hypervolume scaling index `γ_K = ∑_{m=1}^K γ_{mK}` (DLMF 36.6.5). -/
@[dlmf 36.6.E5]
def cuspoidVolumeIndex (K : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 K, cuspoidCoordinateIndex m K

/-- The umbilic hypervolume scaling index `γ^{(U)} = ∑ γ_m^{(U)}` (DLMF 36.6.5). -/
@[dlmf 36.6.E5]
def umbilicVolumeIndex : ℝ := ∑ m : Fin 3, umbilicCoordinateIndex m

/-- The scaled cuspoid coordinates `y(k) = (x_1 k^{γ_{1K}}, …, x_K k^{γ_{KK}})` (DLMF 36.6.2). -/
@[dlmf 36.6.E2]
def cuspoidScaledCoords (K : ℕ) (x : Fin K → ℝ) (k : ℝ) : Fin K → ℝ :=
  fun m => x m * k ^ cuspoidCoordinateIndex ((m : ℕ) + 1) K

end DLMF.CoalescingSaddles
