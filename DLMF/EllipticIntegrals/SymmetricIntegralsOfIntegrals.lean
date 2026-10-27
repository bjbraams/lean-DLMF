/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric

/-!
# Integrals of elliptic integrals (DLMF §19.28)

Mellin transforms on `(0, 1)` of the complete integrals `R_F(0, t, 1)`, `R_G(0, t, 1)`,
`R_D(0, t, 1)` and of the two-variable `R_{-a}(b₁, b₂; t, 1)` (19.28.1)–(19.28.4), with
`B` Mathlib's `Complex.betaIntegral`; and integrals of `R_D`, `R_J`, `R_F` over one of their
variables (19.28.5)–(19.28.10).

All functions are DLMF's (`DLMF.EllipticIntegrals.symEllIntRF` etc. of
`DLMF.EllipticIntegrals.Symmetric`). The integrals are Lebesgue integrals; each left side is
absolutely convergent under the stated hypotheses (the integrands have at worst logarithmic or
integrable power singularities), so the Lean statements carry DLMF's meaning.

**Correction.** DLMF states (19.28.5)–(19.28.9) under "x, y, z, p real and positive". For
(19.28.9), where `x` and `y` are angles, this is not sufficient: numerically (mpmath, 2026-10-25)
the identity holds for `x, y > 0` with `x + y ≤ π/2` and fails beyond, e.g. at
`x = 2, y = 1.3` the two sides are `2.6343` and `6.3569`, and at `x = y = 0.8` they differ by
`0.0918`. The statement below adds the hypothesis `x + y ≤ π/2`.

## §19.28 prose

* 19.28.p1, 19.28.p2: the standing assumptions `ℜσ > 0` and `x, y, z, p > 0`, carried as
  hypotheses.
* 19.28.p3: pointers to (19.16.24) and to Carlson (1963, (7.9)); no further formula.

## References

* NIST DLMF §19.28.
-/

@[expose] public noncomputable section

open Complex Set MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-- DLMF 19.28.1: `∫₀¹ t^{σ-1} R_F(0, t, 1) dt = (1/2) B(σ, 1/2)²`, `ℜσ > 0`. -/
@[dlmf 19.28.E1]
theorem integral_cpow_mul_symEllIntRF_zero {σ : ℂ} (hσ : 0 < σ.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) * symEllIntRF 0 t 1 =
      1 / 2 * betaIntegral σ (1 / 2) ^ 2 := by
  sorry

/-- DLMF 19.28.2: `∫₀¹ t^{σ-1} R_G(0, t, 1) dt = σ/(4σ + 2) B(σ, 1/2)²`, `ℜσ > 0`. -/
@[dlmf 19.28.E2]
theorem integral_cpow_mul_symEllIntRG_zero {σ : ℂ} (hσ : 0 < σ.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) * symEllIntRG 0 t 1 =
      σ / (4 * σ + 2) * betaIntegral σ (1 / 2) ^ 2 := by
  sorry

/-- DLMF 19.28.3: `∫₀¹ t^{σ-1} (1 - t) R_D(0, t, 1) dt = 3/(4σ + 2) B(σ, 1/2)²`, `ℜσ > 0`. -/
@[dlmf 19.28.E3]
theorem integral_cpow_mul_symEllIntRD_zero {σ : ℂ} (hσ : 0 < σ.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) * (1 - t) * symEllIntRD 0 t 1 =
      3 / (4 * σ + 2) * betaIntegral σ (1 / 2) ^ 2 := by
  sorry

/-- DLMF 19.28.4: for real `a`, `b₁`, `b₂` with `c = b₁ + b₂ > 0` and `ℜσ > max(0, a - b₂)`,
`∫₀¹ t^{σ-1} (1 - t)^{c-1} R_{-a}(b₁, b₂; t, 1) dt =
Γ(c) Γ(σ) Γ(σ + b₂ - a) / (Γ(σ + c - a) Γ(σ + b₂))`. Here `R_{-a}` is DLMF's
`symEllIntR a` (on `t ∈ (0, 1)` Carlson's `R`-function). -/
@[dlmf 19.28.E4]
theorem integral_cpow_mul_symEllIntR_two {a b₁ b₂ : ℝ} {σ : ℂ} (hc : 0 < b₁ + b₂)
    (hσ : max 0 (a - b₂) < σ.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) * ((1 - t : ℝ) : ℂ) ^ ((b₁ + b₂ : ℝ) - 1 : ℂ) *
        symEllIntR a ![(b₁ : ℂ), b₂] ![(t : ℂ), 1] =
      Gamma (b₁ + b₂ : ℝ) * Gamma σ * Gamma (σ + b₂ - a) /
        (Gamma (σ + (b₁ + b₂ : ℝ) - a) * Gamma (σ + b₂)) := by
  sorry

/-- DLMF 19.28.5: `∫_z^∞ R_D(x, y, t) dt = 6 R_F(x, y, z)` for `x, y, z > 0`. -/
@[dlmf 19.28.E5]
theorem integral_Ioi_symEllIntRD {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ∫ t in Ioi z, symEllIntRD x y t = 6 * symEllIntRF x y z := by
  sorry

/-- DLMF 19.28.6: `∫₀¹ R_D(x, y, v² z + (1 - v²) p) dv = R_J(x, y, z, p)` for
`x, y, z, p > 0`. -/
@[dlmf 19.28.E6]
theorem integral_symEllIntRD_interp {x y z p : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hp : 0 < p) :
    ∫ v in Ioo (0 : ℝ) 1, symEllIntRD x y (v ^ 2 * z + (1 - v ^ 2) * p : ℝ) =
      symEllIntRJ x y z p := by
  sorry

/-- DLMF 19.28.7: `∫₀^∞ R_J(x, y, z, r²) dr = (3/2) π R_F(xy, xz, yz)` for `x, y, z > 0`. -/
@[dlmf 19.28.E7]
theorem integral_symEllIntRJ_sq {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ∫ r in Ioi (0 : ℝ), symEllIntRJ x y z (r ^ 2 : ℝ) =
      3 / 2 * π * symEllIntRF (x * y : ℝ) (x * z : ℝ) (y * z : ℝ) := by
  sorry

/-- DLMF 19.28.8: `∫₀^∞ R_J(tx, y, z, tp) dt = (6/√p) R_C(p, x) R_F(0, y, z)` for
`x, y, z, p > 0`. -/
@[dlmf 19.28.E8]
theorem integral_symEllIntRJ_scale {x y z p : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hp : 0 < p) :
    ∫ t in Ioi (0 : ℝ), symEllIntRJ (t * x : ℝ) y z (t * p : ℝ) =
      6 / (√p : ℝ) * symEllIntRC p x * symEllIntRF 0 y z := by
  sorry

/-- DLMF 19.28.9, **with the added hypothesis `x + y ≤ π/2`** (see the module docstring; DLMF
assumes only `x, y > 0`, under which the identity is false):
`∫₀^{π/2} R_F(sin²θ cos²(x + y), sin²θ cos²(x - y), 1) dθ = R_F(0, cos²x, 1) R_F(0, cos²y, 1)`. -/
@[dlmf 19.28.E9]
theorem integral_symEllIntRF_sin_cos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y ≤ π / 2) :
    ∫ θ in Ioo (0 : ℝ) (π / 2),
        symEllIntRF (Real.sin θ ^ 2 * Real.cos (x + y) ^ 2 : ℝ)
          (Real.sin θ ^ 2 * Real.cos (x - y) ^ 2 : ℝ) 1 =
      symEllIntRF 0 (Real.cos x ^ 2 : ℝ) 1 * symEllIntRF 0 (Real.cos y ^ 2 : ℝ) 1 := by
  sorry

/-- DLMF 19.28.10: for `a, b, c, d > 0`,
`∫₀^∞ R_F((ac + bd)², (ad + bc)², 4abcd cosh² z) dz = (1/2) R_F(0, a², b²) R_F(0, c², d²)`. -/
@[dlmf 19.28.E10]
theorem integral_symEllIntRF_cosh {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    ∫ z in Ioi (0 : ℝ),
        symEllIntRF ((a * c + b * d) ^ 2 : ℝ) ((a * d + b * c) ^ 2 : ℝ)
          (4 * a * b * c * d * Real.cosh z ^ 2 : ℝ) =
      1 / 2 * symEllIntRF 0 (a ^ 2 : ℝ) (b ^ 2 : ℝ) * symEllIntRF 0 (c ^ 2 : ℝ) (d ^ 2 : ℝ) := by
  sorry

end DLMF.EllipticIntegrals
