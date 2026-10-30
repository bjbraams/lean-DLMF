/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Basic.Equations

/-!
# Lamé boundary conditions, eigenvalues and normalized eigenfunctions
-/

@[expose] public noncomputable section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Set Filter
open scoped Real Topology

namespace DLMF.Lame

/-! ### The eigenvalue problems (§29.3) -/

/-- The boundary conditions of Table 29.3.2 on `[0, K]`, `K = K(k)`: at `x = 0`, `w(0) = 0` if
`odd0` and `w'(0) = 0` otherwise; at `x = K`, `w(K) = 0` if `oddK` and `w'(K) = 0` otherwise. -/
def Real.LameBoundary (k : ℝ) (odd0 oddK : Bool) (w : ℝ → ℝ) : Prop :=
  (if odd0 then w 0 = 0 else deriv w 0 = 0) ∧
    (if oddK then w (Real.compEllIntKm (k ^ 2)) = 0 else deriv w (Real.compEllIntKm (k ^ 2)) = 0)

/-- `w` is an eigenfunction of the Lamé problem with eigenvalue `h` and boundary types
`odd0`, `oddK` (Table 29.3.2): a nonzero real solution of 29.2.1 satisfying the boundary
conditions. -/
def Real.IsLameEigenfunction (h ν k : ℝ) (odd0 oddK : Bool) (w : ℝ → ℝ) : Prop :=
  Real.IsLameSolution h ν k w ∧ Real.LameBoundary k odd0 oddK w ∧ w ≠ 0

/-- The spectrum of the Lamé problem with boundary types `odd0`, `oddK` (§29.3(i)). -/
def Real.lameSpectrum (ν k : ℝ) (odd0 oddK : Bool) : Set ℝ :=
  {h | ∃ w, Real.IsLameEigenfunction h ν k odd0 oddK w}

/-- `h` is the `j`th eigenvalue (counting from `0`) of the problem `odd0`, `oddK`: it lies in
the spectrum and exactly `j` points of the spectrum lie below it. -/
def Real.IsNthLameEigenvalue (ν k : ℝ) (odd0 oddK : Bool) (j : ℕ) (h : ℝ) : Prop :=
  h ∈ Real.lameSpectrum ν k odd0 oddK ∧ (Real.lameSpectrum ν k odd0 oddK ∩ Set.Iio h).Finite ∧
    (Real.lameSpectrum ν k odd0 oddK ∩ Set.Iio h).ncard = j

/-- The `j`th eigenvalue of the Lamé problem with boundary types `odd0`, `oddK` (§29.3(i)),
defined by choice as the unique `h` with `IsNthLameEigenvalue` (junk value `0` if there is
none; existence is `Real.lameEigenvalue_spec`). -/
def Real.lameEigenvalue (ν k : ℝ) (odd0 oddK : Bool) (j : ℕ) : ℝ :=
  open Classical in
  if hx : ∃! h, Real.IsNthLameEigenvalue ν k odd0 oddK j h then hx.exists.choose else 0

/-- The eigenvalue `a^m_ν(k²)` (DLMF §29.3(i), Table 29.3.1): `a^{2j}` is the `j`th eigenvalue
of the problem `w'(0) = w'(K) = 0`, `a^{2j+1}` that of `w(0) = w'(K) = 0`. -/
@[dlmf 29.3.i]
def Real.lameAk (ν : ℝ) (m : ℕ) (k : ℝ) : ℝ := Real.lameEigenvalue ν k m.bodd false (m / 2)

/-- The eigenvalue `b^m_ν(k²)`, `m ≥ 1` (DLMF §29.3(i), Table 29.3.1): `b^{2j+1}` is the `j`th
eigenvalue of the problem `w'(0) = w(K) = 0`, `b^{2j+2}` that of `w(0) = w(K) = 0`. The value
at `m = 0` is not used. -/
@[dlmf 29.3.i]
def Real.lameBk (ν : ℝ) (m : ℕ) (k : ℝ) : ℝ :=
  Real.lameEigenvalue ν k (!m.bodd) true ((m - 1) / 2)

/-- `w` is the normalized `j`th eigenfunction of the problem `odd0`, `oddK`: an eigenfunction
for `Real.lameEigenvalue ν k odd0 oddK j`, normalized by DLMF 29.3.18,
`∫₀^K dn(x, k) w(x)² dx = π/4`, with the sign rule of §29.3(v): `w(K) > 0` if `w'(K) = 0`
(`Ec`) and `w'(K) < 0` if `w(K) = 0` (`Es`). -/
def Real.IsNormalizedLameEigenfunction (ν k : ℝ) (odd0 oddK : Bool) (j : ℕ) (w : ℝ → ℝ) :
    Prop :=
  Real.IsLameEigenfunction (Real.lameEigenvalue ν k odd0 oddK j) ν k odd0 oddK w ∧
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.jacobiDnm x (k ^ 2) * w x ^ 2 = π / 4 ∧
    (if oddK then deriv w (Real.compEllIntKm (k ^ 2)) < 0 else 0 < w (Real.compEllIntKm (k ^ 2)))

/-- The normalized `j`th eigenfunction of the Lamé problem `odd0`, `oddK`, defined by choice
(junk value `0` if it does not exist uniquely; see `Real.lameEigenfunction_spec`). -/
def Real.lameEigenfunction (ν k : ℝ) (odd0 oddK : Bool) (j : ℕ) : ℝ → ℝ :=
  open Classical in
  if hx : ∃! w, Real.IsNormalizedLameEigenfunction ν k odd0 oddK j w then hx.exists.choose
  else 0

/-- The Lamé function `Ec^m_ν(x, k²)` for real `x` (DLMF §29.3(iv), Table 29.3.2): the
eigenfunction for `a^m_ν(k²)`, normalized by 29.3.18 and `Ec^m_ν(K, k²) > 0`. -/
@[dlmf 29.3.iv]
def Real.lameEck (ν : ℝ) (m : ℕ) (x k : ℝ) : ℝ :=
  Real.lameEigenfunction ν k m.bodd false (m / 2) x

/-- The Lamé function `Es^m_ν(x, k²)`, `m ≥ 1`, for real `x` (DLMF §29.3(iv), Table 29.3.2):
the eigenfunction for `b^m_ν(k²)`, normalized by 29.3.18 and `dEs^m_ν(z, k²)/dz < 0` at
`z = K`. -/
@[dlmf 29.3.iv]
def Real.lameEsk (ν : ℝ) (m : ℕ) (x k : ℝ) : ℝ :=
  Real.lameEigenfunction ν k (!m.bodd) true ((m - 1) / 2) x

end DLMF.Lame
