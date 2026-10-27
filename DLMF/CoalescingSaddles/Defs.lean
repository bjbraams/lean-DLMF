/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Basic
public import DLMF.Airy.Basic

/-!
# Integrals with coalescing saddles: definitions for DLMF §§36.7–36.11

Definitions used by the part B files of DLMF Chapter 36 (namespace `DLMF.CoalescingSaddles`);
the canonical integrals themselves are in `DLMF.CoalescingSaddles.Basic`.

* **Moments** (helpers for §36.10). `cuspoidMoment K x p = ∫ d(r) t(r)^p exp(iΦ_K(t(r); x)) dr`
  over the rotated contour `t(r) = r d(r)` of `cuspoidIntegral`, so that
  `cuspoidMoment K x 0 = Ψ_K(x)`, and `hyperbolicUmbilicMoment x y z a b`, the analogous
  moment `∫∫ s^a t^b exp(iΦ^{(H)})` over the contour of `hyperbolicUmbilicIntegral`.
* **Convergent series** (§36.8). The coefficients `a_n(x)` of 36.8.2
  (`cuspoidSeriesCoeff`), the polynomials `c_n, d_n` of 36.8.6 (`umbilicSeriesC`,
  `umbilicSeriesD`) and the functions `f_n` of 36.8.5 (`ellipticUmbilicSeriesF`).
* **Zeros** (§36.7). The approximate zero loci printed by DLMF: 36.7.1 (inside the cusp),
  36.7.2–36.7.3 (outside the cusp), 36.7.4–36.7.7 (the ring lattice of the elliptic umbilic)
  and 36.7.8 (the zero lines of `Ψ^{(E)}` in the plane `z = 0`). Signs `±` are units of `ℤ`.
* **Stationary phase** (§36.11). `cuspoidStationaryPhaseSum K x`, the right-hand side of
  36.11.2 without the factors `1 + o(1)`.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace DLMF.CoalescingSaddles

/-! ### Moments of the canonical integrands (helpers for §36.10) -/

/-- The `p`-th moment `∫ d(r) t(r)^p exp(iΦ_K(t(r); x)) dr` of the cuspoid integrand over the
rotated contour `t(r) = cuspoidContour K r` (with `d(r) = cuspoidContourDir K r`); it is the
contour form of `∫ t^p exp(iΦ_K(t; x)) dt`, and `cuspoidMoment K x 0 = cuspoidIntegral K x`. -/
def cuspoidMoment (K : ℕ) (x : Fin K → ℝ) (p : ℕ) : ℂ :=
  ∫ r : ℝ, cuspoidContourDir K r * cuspoidContour K r ^ p *
    exp (I * cuspoidPotential K (cuspoidContour K r) x)

/-- The moment `∫∫ s^a t^b exp(iΦ^{(H)}(s, t; x)) ds dt` of the hyperbolic umbilic integrand over
the product of cubic V-contours used in `hyperbolicUmbilicIntegral`. -/
def hyperbolicUmbilicMoment (x y z : ℝ) (a b : ℕ) : ℂ :=
  ∫ p : ℝ × ℝ, cuspoidContourDir 1 p.1 * cuspoidContourDir 1 p.2 *
    (cuspoidContour 1 p.1 ^ a * cuspoidContour 1 p.2 ^ b) *
    exp (I * hyperbolicUmbilicPotential (cuspoidContour 1 p.1) (cuspoidContour 1 p.2) x y z)

/-! ### Coefficients of the convergent series (§36.8) -/

/-- The coefficients `a_n(x)` of the cuspoid series 36.8.1, defined by the recurrence 36.8.2:
`a_0 = 1`, `a_{n+1} = (i/(n+1)) ∑_{p=0}^{min(n, K-1)} (p+1) x_{p+1} a_{n-p}`. In Lean the index
`p` runs over `Fin (min (n+1) K)` (the same range, and empty when `K = 0`), and DLMF's `x_{p+1}`
is `x p`. They are the Maclaurin coefficients of `exp(i ∑ₘ xₘ tᵐ)`. -/
@[dlmf 36.8.E2]
def cuspoidSeriesCoeff (K : ℕ) (x : Fin K → ℝ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => I / ((n : ℂ) + 1) * ∑ p : Fin (min (n + 1) K),
      (((p : ℕ) : ℂ) + 1) * ((x ⟨p, lt_of_lt_of_le p.isLt (min_le_right _ _)⟩ : ℝ) : ℂ) *
        cuspoidSeriesCoeff K x (n - p)
  decreasing_by omega

/-- The pair `(c_n, d_n)` of polynomials of 36.8.6. -/
def umbilicSeriesCD : ℕ → Polynomial ℂ × Polynomial ℂ
  | 0 => (1, 0)
  | n + 1 => (Polynomial.derivative (umbilicSeriesCD n).1 + Polynomial.X * (umbilicSeriesCD n).2,
      (umbilicSeriesCD n).1 + Polynomial.derivative (umbilicSeriesCD n).2)

/-- The polynomials `c_n(t)` of 36.8.6: `c_0 = 1`, `c_{n+1} = c_n' + t d_n`. -/
@[dlmf 36.8.E6]
def umbilicSeriesC (n : ℕ) : Polynomial ℂ := (umbilicSeriesCD n).1

/-- The polynomials `d_n(t)` of 36.8.6: `d_0 = 0`, `d_{n+1} = c_n + d_n'`. -/
@[dlmf 36.8.E6]
def umbilicSeriesD (n : ℕ) : Polynomial ℂ := (umbilicSeriesCD n).2

/-- The functions `f_n(ζ, ζ')` of 36.8.5 (DLMF writes `f_n(ζ, ζ̄)` and evaluates at
`ζ' = ζ̄`):
`f_n = c_n(ζ)c_n(ζ')Ai(ζ)Bi(ζ') + c_n(ζ)d_n(ζ')Ai(ζ)Bi'(ζ') + d_n(ζ)c_n(ζ')Ai'(ζ)Bi(ζ')
  + d_n(ζ)d_n(ζ')Ai'(ζ)Bi'(ζ')`. -/
@[dlmf 36.8.E5]
def ellipticUmbilicSeriesF (n : ℕ) (ζ ζ' : ℂ) : ℂ :=
  (umbilicSeriesC n).eval ζ * (umbilicSeriesC n).eval ζ' * Airy.airyAi ζ * Airy.airyBi ζ' +
    (umbilicSeriesC n).eval ζ * (umbilicSeriesD n).eval ζ' * Airy.airyAi ζ *
      Airy.airyBiDeriv ζ' +
    (umbilicSeriesD n).eval ζ * (umbilicSeriesC n).eval ζ' * Airy.airyAiDeriv ζ *
      Airy.airyBi ζ' +
    (umbilicSeriesD n).eval ζ * (umbilicSeriesD n).eval ζ' * Airy.airyAiDeriv ζ *
      Airy.airyBiDeriv ζ'

/-! ### Approximate zeros (§36.7) -/

/-- The ordinate `y_m = -√(2π(2m+1))`, `m = 1, 2, …`, of the `m`-th curved row of zeros of the
Pearcey integral inside the cusp, close to the `y`-axis (DLMF 36.7.1, approximate). -/
@[dlmf 36.7.E1]
def cuspInnerZeroY (m : ℕ) : ℝ := -Real.sqrt (2 * π * (2 * m + 1))

/-- The abscissae `x^±_{m,n} = √(2/(-y_m)) (2n + 1/2 + (-1)^m/2 ± 1/4) π`, `m = 1, 2, …`,
`n ∈ ℤ`, of the pairs of zeros of the Pearcey integral inside the cusp (DLMF 36.7.1,
approximate); the sign `±` is the unit `σ : ℤˣ`. -/
@[dlmf 36.7.E1]
def cuspInnerZeroX (m : ℕ) (n : ℤ) (σ : ℤˣ) : ℝ :=
  Real.sqrt (2 / -cuspInnerZeroY m) *
    (2 * n + 1 / 2 + (-1 : ℝ) ^ m / 2 + ((σ : ℤ) : ℝ) / 4) * π

/-- The equation 36.7.3 for the parameter `ξ_n` of the zeros outside the cusp:
`3π(8n+5)/(9+8ξ) · ξ^{3/2} = (27/16)(3/2)^{1/2} (ln(1/ξ) + 3 ln(3/2))`. DLMF takes `ξ_n` to be
"the real solution"; it exists and is unique among `ξ > 0`
(`existsUnique_cuspOuterZeroParam`). -/
@[dlmf 36.7.E3]
def IsCuspOuterZeroParam (n : ℕ) (ξ : ℝ) : Prop :=
  3 * π * (8 * n + 5) / (9 + 8 * ξ) * ξ ^ (3 / 2 : ℝ) =
    27 / 16 * Real.sqrt (3 / 2) * (Real.log (1 / ξ) + 3 * Real.log (3 / 2))

/-- The ordinate `y_n = -(3π(8n+5)/(9+8ξ_n))^{1/2}`, `n = 0, 1, …`, of the zeros just outside the
cusp (DLMF 36.7.2, approximate), as a function of the parameter `ξ = ξ_n` of 36.7.3. -/
@[dlmf 36.7.E2]
def cuspOuterZeroY (n : ℕ) (ξ : ℝ) : ℝ := -Real.sqrt (3 * π * (8 * n + 5) / (9 + 8 * ξ))

/-- The abscissa `x_n = ±(8/27)^{1/2} |y_n|^{3/2} (1 + ξ_n)` of the zeros just outside the cusp
(DLMF 36.7.2, approximate); the sign `±` is the unit `σ : ℤˣ`. -/
@[dlmf 36.7.E2]
def cuspOuterZeroX (n : ℕ) (ξ : ℝ) (σ : ℤˣ) : ℝ :=
  ((σ : ℤ) : ℝ) * Real.sqrt (8 / 27) * |cuspOuterZeroY n ξ| ^ (3 / 2 : ℝ) * (1 + ξ)

/-- The planes `z = ±z_n`, `z_n = 3(π(2n - 1/2)/4)^{1/3}`, `n = 1, 2, …`, near which the zero
rings of the elliptic umbilic integral lie, deep inside the bifurcation set (DLMF 36.7.4,
approximate; DLMF's decimal form `3.48734 (n - 1/4)^{1/3}` is excluded as numerical). -/
@[dlmf 36.7.E4]
def ellipticUmbilicRingPlane (n : ℕ) : ℝ := 3 * (π / 4 * (2 * n - 1 / 2)) ^ (1 / 3 : ℝ)

/-- The `z` repeat distance `Δz = 9π/(2 z_n²)` of the ring lattice near `z = z_n`
(DLMF 36.7.5). -/
@[dlmf 36.7.E5]
def ellipticUmbilicLatticeDz (zn : ℝ) : ℝ := 9 * π / (2 * zn ^ 2)

/-- The `x` repeat distance `Δx = 6π/z_n` of the ring lattice near `z = z_n` (DLMF 36.7.5). -/
@[dlmf 36.7.E5]
def ellipticUmbilicLatticeDx (zn : ℝ) : ℝ := 6 * π / zn

/-- The left-hand side of 36.7.6,
`exp(-2πi((z - z_n)/Δz + 2x/Δx)) (2 exp(-6πix/Δx) cos(2√3πy/Δx) + 1)`, with `z_n`, `Δz`, `Δx`
from 36.7.4–36.7.5; the zeros of `Ψ^{(E)}` near `z = z_n` are approximated by the solutions of
`ellipticUmbilicRingEquation n x y z = √3` (DLMF 36.7.6). -/
@[dlmf 36.7.E6]
def ellipticUmbilicRingEquation (n : ℕ) (x y z : ℝ) : ℂ :=
  let zn := ellipticUmbilicRingPlane n
  let Dz := ellipticUmbilicLatticeDz zn
  let Dx := ellipticUmbilicLatticeDx zn
  exp (-2 * π * I * (((z - zn) / Dz + 2 * x / Dx : ℝ) : ℂ)) *
    (2 * exp (-6 * π * I * ((x / Dx : ℝ) : ℂ)) *
      ((Real.cos (2 * Real.sqrt 3 * π * y / Dx) : ℝ) : ℂ) + 1)

/-- The number `n_max(m) = ⌊(256/13) m - 269/52⌋` of zero rings in the `m`-th row of a symmetry
plane, before the transition to hairpins (DLMF 36.7.7, an empirical count). -/
@[dlmf 36.7.E7]
def ellipticUmbilicRingCount (m : ℕ) : ℤ := ⌊(256 / 13 : ℝ) * m - 269 / 52⌋

/-- The leading term `3((2n-1)π/(4|sin(3θ/2)|))^{2/3}` of the radius of the `n`-th zero of
`Ψ^{(E)}(r cos θ, r sin θ, 0)` (DLMF 36.7.8). -/
@[dlmf 36.7.E8]
def ellipticUmbilicPlaneZeroRadius (n : ℕ) (θ : ℝ) : ℝ :=
  3 * ((2 * n - 1) * π / (4 * |Real.sin (3 / 2 * θ)|)) ^ (2 / 3 : ℝ)

/-! ### Stationary phase (§36.11) -/

/-- The leading-order stationary-phase sum of 36.11.2,
`√(2π) ∑ⱼ exp(i(Φ_K(tⱼ; x) + ¼π(-1)^{j+K+1})) |∂²Φ_K(tⱼ; x)/∂t²|^{-1/2}`, over the real critical
points `t₁ < t₂ < ⋯` of `Φ_K(·; x)` (DLMF 36.11.1). The sign `(-1)^{j+K+1}` of DLMF is written as
the sign of `∂²Φ_K/∂t²(tⱼ)`: the leading coefficient of `∂Φ_K/∂t` is positive and its degree is
`K + 1`, so at simple critical points the signs of `∂²Φ_K/∂t²` alternate and that at `t₁` is
`(-1)^K`. The sum is a `finsum` over the (finite) set of real critical points. -/
@[dlmf 36.11.E1, dlmf 36.11.E2]
def cuspoidStationaryPhaseSum (K : ℕ) (x : Fin K → ℝ) : ℂ :=
  (Real.sqrt (2 * π) : ℂ) * ∑ᶠ t ∈ cuspoidCriticalPoints K x,
    exp (I * (cuspoidPotential K (t : ℂ) x +
      π / 4 * (SignType.sign (iteratedDeriv 2 (fun u => cuspoidPotential K u x) (t : ℂ)).re :
        ℝ))) *
      ((‖iteratedDeriv 2 (fun u => cuspoidPotential K u x) (t : ℂ)‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

end DLMF.CoalescingSaddles
