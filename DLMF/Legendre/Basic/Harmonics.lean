/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Basic
public import DLMF.OrthogonalPolynomials.Basic.Definitions

/-!
# Spherical and surface harmonics as functions of angles (DLMF §14.30)

## Main definitions

* `ferrersPNat`: the Ferrers function `𝖯^m_l` of integer degree and order, through the
  derivatives of the Legendre polynomial (DLMF 14.7.8); it is continuous at both endpoints.
* `sphericalHarmonicNonneg`, `sphericalHarmonic`: the spherical harmonic `Y_{l,m}(θ, φ)`
  (DLMF 14.30.1).
* `surfaceHarmonic`: the real surface harmonics of the first kind (DLMF 14.30.2).

## Implementation notes

`sphericalHarmonic l m` is defined as `0` when `|m| > l`. The harmonic homogeneous polynomials of
AAR Chapter 9 are in `DLMF.SphericalHarmonics.Basic`; the properties of the functions here
(orthonormality, the addition theorem) are in `DLMF.Legendre.Harmonics`.
-/

@[expose] public noncomputable section

open Complex

open scoped Real

namespace DLMF.Legendre

open DLMF.OrthogonalPolynomials

/-- Polynomial definition extends integral-degree Ferrers P continuously to both endpoints. -/
def ferrersPNat (l m : ℕ) (x : ℝ) : ℂ :=
  (-1)^m*(Real.sqrt (1-x^2):ℂ)^m*iteratedDeriv m (legendrePolyP l) x

/-- DLMF 14.30.1 for `m ≥ 0`: the spherical harmonic `Y_{l,m}(θ, φ) = √((l-m)! (2l+1)/(4π (l+m)!))
e^{imφ} 𝖯^m_l(cos θ)`. -/
@[dlmf 14.30.E1]
def sphericalHarmonicNonneg (l m : ℕ) (θ phi : ℝ) : ℂ :=
  Real.sqrt (((l-m).factorial:ℝ)*(2*l+1)/(4*π*(l+m).factorial))*exp (I*m*phi)*
    ferrersPNat l m (Real.cos θ)

/-- DLMF 14.30.1: the spherical harmonic `Y_{l,m}(θ, φ)` for integer `m`, equal to
`sphericalHarmonicNonneg l m` for `m ≥ 0`, to `(-1)^{|m|}` times the complex conjugate of
`Y_{l,|m|}` for `m < 0`, and to `0` when `|m| > l`. -/
@[dlmf 14.30.E1]
def sphericalHarmonic (l : ℕ) (m : ℤ) (θ phi : ℝ) : ℂ :=
  if l < m.natAbs then 0
  else if m < 0 then (-1)^m.natAbs*star (sphericalHarmonicNonneg l m.natAbs θ phi)
  else sphericalHarmonicNonneg l m.natAbs θ phi

/-- DLMF 14.30.2: the real surface harmonic of the first kind `cos(mφ) 𝖯^m_l(cos θ)` (or `sin(mφ)
𝖯^m_l(cos θ)` when `sine` is true), for natural `l, m`. -/
@[dlmf 14.30.E2]
def surfaceHarmonic (sine : Bool) (l m : ℕ) (θ phi : ℝ) : ℂ :=
  (if sine then Real.sin (m*phi) else Real.cos (m*phi))*ferrersPNat l m (Real.cos θ)

end DLMF.Legendre
