/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic
public import DLMF.Weierstrass.Basic
public import DLMF.Elliptic.Jacobi

/-!
# Lamé functions: definitions (DLMF §§29.1–29.3, 29.6, 29.9, 29.11)

DLMF Chapter 29 studies Lamé's equation (29.2.1)
`w'' + (h - ν(ν+1) k² sn²(z, k)) w = 0`, `0 < k < 1`, `ν ≥ -1/2`,
its eigenvalues `a^m_ν(k²)`, `b^m_ν(k²)` and eigenfunctions `Ec^m_ν(z, k²)`, `Es^m_ν(z, k²)`.

## Design

* **Equations.** `IsLameSolutionOn h ν k w U` is 29.2.1 over `ℂ` on a set `U` with the
  project's complex `sn(z, k) = DLMF.JacobiElliptic.jacobiSnk z k` (modulus `k`); like
  `DLMF.Painleve.IsPIIOn` it records genuine differentiability of `w` and `w'`, so totalized
  derivatives cannot make a nonsolution satisfy the equation. The other forms of §29.2
  (algebraic 29.2.2, trigonometric 29.2.4, Weierstrass 29.2.9 and 29.2.10) and the Lamé wave
  equation 29.11.1 have their own predicates. `Real.IsLameSolution h ν k w` is 29.2.1 for real
  `x ∈ ℝ` with the real-variable `sn = DLMF.Elliptic.Real.jacobiSnm x (k²)` (parameter
  `m = k²`; it agrees with the complex `sn` for `0 < k < 1`, `jacobiSnk_ofReal`).
* **Eigenvalues.** Table 29.3.2 describes the four eigenvalue families as the four
  Sturm–Liouville problems on `[0, K]` with Neumann (`w' = 0`, "even") or Dirichlet (`w = 0`,
  "odd") conditions at `0` and at `K = K(k)`. `Real.lameEigenvalue ν k odd0 oddK j` is the
  `j`th element (from `0`) of the spectrum of the problem with boundary types `odd0`, `oddK`:
  the unique `h` in the spectrum with exactly `j` spectral points below it
  (`if h : ∃! … then … else 0`; **definition by choice**, the existence and the ordering of
  the spectrum are the admitted theorem `Real.lameEigenvalue_spec` in `DLMF.Lame.Eigenvalues`).
  Then `a^{2m} = (even, even, m)`, `a^{2m+1} = (odd, even, m)`, `b^{2m+1} = (even, odd, m)`,
  `b^{2m+2} = (odd, odd, m)` (`Real.lameAk`, `Real.lameBk`; the superscript of DLMF is the
  natural number argument, `b^0` is not used).
* **Eigenfunctions.** `Real.lameEigenfunction ν k odd0 oddK j` is the unique real eigenfunction
  for that eigenvalue normalized by 29.3.18, `∫₀^K dn(x, k) w(x)² dx = π/4`, with the sign rule
  of §29.3(v) (`w(K) > 0` for `Ec`, `w'(K) < 0` for `Es`); **definition by choice**, existence
  and uniqueness are the admitted theorem `Real.lameEigenfunction_spec`. `Real.lameEck` and
  `Real.lameEsk` are DLMF's `Ec^m_ν(x, k²)` and `Es^m_ν(x, k²)` for real `x`. Lamé functions are
  real-variable functions here: DLMF's eigenvalue problem, normalization, orthogonality,
  Fourier series in `φ = π/2 - am(x, k)` and integral equations are all on the real line.
  The Lamé polynomials (§29.12), which are meromorphic in `z`, are explicit complex functions in
  `DLMF.Lame.Polynomials.Defs`.
* **Parameters.** Every function takes the modulus `k` (DLMF writes `k²`); argument order is
  `ν` (subscript), `m` (superscript), `x`, `k`, as for `ferrersP ν μ x`.
* **Recurrences.** The coefficients `α_p, β_p, γ_p` of the eight three-term recurrences of
  29.3.11–29.3.17 and 29.6.11, 29.6.26, 29.6.41, 29.6.56 are `LameRecurrence.alpha/beta/gamma`;
  the finite continued fractions of 29.3.10 are `lameCFLeft`, `lameCFRight`; the Fourier
  coefficients of 29.6 are defined by the Fourier integrals in `Real.lameCosCoeff`,
  `Real.lameSinCoeff`.

Mathlib and TauCeti have no Lamé functions (checked 2026-10-26).
-/

@[expose] public section

open Complex DLMF.JacobiElliptic DLMF.Elliptic
open scoped Real

noncomputable section

namespace DLMF.Lame

/-! ### Lamé's equation and its other forms (§29.2) -/

/-- Lamé's equation (DLMF 29.2.1) over `ℂ` on a set `U`:
`w'' + (h - ν(ν+1) k² sn²(z, k)) w = 0`, with `w` and `w'` complex differentiable at every
point of `U`. DLMF takes `0 < k < 1`, `ν ≥ -1/2` and `h` real; the predicate is stated for all
complex parameters. -/
@[dlmf 29.2.E1]
structure IsLameSolutionOn (h ν k : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  differentiableAt : ∀ z ∈ U, DifferentiableAt ℂ w z
  hasDerivAt_deriv : ∀ z ∈ U,
    HasDerivAt (deriv w) (-(h - ν * (ν + 1) * k ^ 2 * jacobiSnk z k ^ 2) * w z) z

/-- The algebraic form of Lamé's equation (DLMF 29.2.2) in `ξ = sn²(z, k)` (29.2.3):
`w'' + ½(1/ξ + 1/(ξ-1) + 1/(ξ-k⁻²)) w' + (h k⁻² - ν(ν+1)ξ)/(4ξ(ξ-1)(ξ-k⁻²)) w = 0` on `U`. -/
@[dlmf 29.2.E2]
structure IsLameAlgebraicSolutionOn (h ν k : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  differentiableAt : ∀ ξ ∈ U, DifferentiableAt ℂ w ξ
  hasDerivAt_deriv : ∀ ξ ∈ U, HasDerivAt (deriv w)
    (-(1 / 2 * (1 / ξ + 1 / (ξ - 1) + 1 / (ξ - (k ^ 2)⁻¹)) * deriv w ξ) -
      (h * (k ^ 2)⁻¹ - ν * (ν + 1) * ξ) / (4 * ξ * (ξ - 1) * (ξ - (k ^ 2)⁻¹)) * w ξ) ξ

/-- The Weierstrass form of Lamé's equation (DLMF 29.2.9) in `η`:
`w'' + (g - ν(ν+1) ℘(η; g₂, g₃)) w = 0` on `U`, with the project's `℘(η; g₂, g₃)`
(`DLMF.Weierstrass.weierstrassPInvariants`). -/
@[dlmf 29.2.E9]
structure IsLameWeierstrassSolutionOn (g ν g₂ g₃ : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  differentiableAt : ∀ η ∈ U, DifferentiableAt ℂ w η
  hasDerivAt_deriv : ∀ η ∈ U, HasDerivAt (deriv w)
    (-(g - ν * (ν + 1) * DLMF.Weierstrass.weierstrassPInvariants g₂ g₃ η) * w η) η

/-- The algebraic Weierstrass form of Lamé's equation (DLMF 29.2.10) in `ζ = ℘(η)`:
`w'' + ½ ∑ⱼ 1/(ζ - eⱼ) w' + (g - ν(ν+1)ζ)/(4 ∏ⱼ (ζ - eⱼ)) w = 0` on `U`. -/
@[dlmf 29.2.E10]
structure IsLameWeierstrassAlgebraicSolutionOn (g ν e₁ e₂ e₃ : ℂ) (w : ℂ → ℂ) (U : Set ℂ) :
    Prop where
  differentiableAt : ∀ ζ ∈ U, DifferentiableAt ℂ w ζ
  hasDerivAt_deriv : ∀ ζ ∈ U, HasDerivAt (deriv w)
    (-(1 / 2 * (1 / (ζ - e₁) + 1 / (ζ - e₂) + 1 / (ζ - e₃)) * deriv w ζ) -
      (g - ν * (ν + 1) * ζ) / (4 * (ζ - e₁) * (ζ - e₂) * (ζ - e₃)) * w ζ) ζ

/-- The Lamé (ellipsoidal) wave equation (DLMF 29.11.1) on `U`:
`w'' + (h - ν(ν+1) k² sn²(z, k) + k² ω² sn⁴(z, k)) w = 0`. -/
@[dlmf 29.11.E1]
structure IsLameWaveSolutionOn (h ν k ω : ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop where
  differentiableAt : ∀ z ∈ U, DifferentiableAt ℂ w z
  hasDerivAt_deriv : ∀ z ∈ U, HasDerivAt (deriv w)
    (-(h - ν * (ν + 1) * k ^ 2 * jacobiSnk z k ^ 2 + k ^ 2 * ω ^ 2 * jacobiSnk z k ^ 4) * w z) z

/-- Lamé's equation (DLMF 29.2.1) for real `x ∈ ℝ` and real parameters, with the real
`sn(x, k) = Real.jacobiSnm x (k²)`: `w` is differentiable on `ℝ` and
`w'' = -(h - ν(ν+1) k² sn²(x, k)) w` everywhere. -/
@[dlmf 29.2.E1 "real form: real x, real h, ν, k"]
structure Real.IsLameSolution (h ν k : ℝ) (w : ℝ → ℝ) : Prop where
  differentiable : Differentiable ℝ w
  hasDerivAt_deriv : ∀ x : ℝ,
    HasDerivAt (deriv w) (-(h - ν * (ν + 1) * k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2) * w x) x

/-- The trigonometric form of Lamé's equation (DLMF 29.2.4) for real `φ`:
`(1 - k² cos²φ) w'' + k² cos φ sin φ w' + (h - ν(ν+1) k² cos²φ) w = 0`. -/
@[dlmf 29.2.E4]
structure Real.IsLameTrigSolution (h ν k : ℝ) (w : ℝ → ℝ) : Prop where
  differentiable : Differentiable ℝ w
  differentiable_deriv : Differentiable ℝ (deriv w)
  ode : ∀ φ : ℝ, (1 - k ^ 2 * Real.cos φ ^ 2) * deriv (deriv w) φ +
    k ^ 2 * Real.cos φ * Real.sin φ * deriv w φ +
      (h - ν * (ν + 1) * k ^ 2 * Real.cos φ ^ 2) * w φ = 0

/-- The variable `φ = π/2 - am(x, k)` of DLMF 29.2.5 for real `x` (`am` is the real amplitude
`Real.jacobiAmm x (k²)` of §22.16(i)); then `cos φ = sn(x, k)` and `sin φ = cn(x, k)`. -/
@[dlmf 29.2.E5]
def Real.lamePhi (x k : ℝ) : ℝ := π / 2 - Real.jacobiAmm x (k ^ 2)

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

/-! ### Three-term recurrences and continued fractions (§§29.3(iii), 29.6) -/

/-- The eight three-term recurrences of DLMF §§29.3(iii) and 29.6: `A0` (29.3.11–29.3.12, for
`a^{2m}`, coefficients `A_{2p}`), `A1` (29.3.13–29.3.14, `a^{2m+1}`, `A_{2p+1}`), `B1`
(29.3.15–29.3.16, `b^{2m+1}`, `B_{2p+1}`), `B2` (29.3.17, `b^{2m+2}`, `B_{2p+2}`), `C0`
(29.6.11, `a^{2m}`, `C_{2p}`), `C1` (29.6.26, `a^{2m+1}`, `C_{2p+1}`), `D1` (29.6.41,
`b^{2m+1}`, `D_{2p+1}`) and `D2` (29.6.56, `b^{2m+2}`, `D_{2p+2}`). -/
inductive LameRecurrence
  | A0 | A1 | B1 | B2 | C0 | C1 | D1 | D2
  deriving DecidableEq

namespace LameRecurrence

/-- The coefficient `α_p` (DLMF 29.3.11, 29.3.14, 29.3.16, 29.3.17, 29.6.11, 29.6.26, 29.6.41,
29.6.56). -/
@[dlmf 29.3.E11, dlmf 29.3.E14, dlmf 29.3.E16, dlmf 29.3.E17, dlmf 29.6.E11, dlmf 29.6.E26,
  dlmf 29.6.E41, dlmf 29.6.E56]
def alpha : LameRecurrence → ℝ → ℝ → ℕ → ℝ
  | A0, ν, k, p =>
      if p = 0 then (ν - 1) * (ν + 2) * k ^ 2 else (ν - 2 * p - 1) * (ν + 2 * p + 2) * k ^ 2 / 2
  | A1, ν, k, p => (ν - 2 * p - 2) * (ν + 2 * p + 3) * k ^ 2 / 2
  | B1, ν, k, p => (ν - 2 * p - 2) * (ν + 2 * p + 3) * k ^ 2 / 2
  | B2, ν, k, p => (ν - 2 * p - 3) * (ν + 2 * p + 4) * k ^ 2 / 2
  | C0, ν, k, p =>
      if p = 0 then ν * (ν + 1) * k ^ 2 else (ν - 2 * p) * (ν + 2 * p + 1) * k ^ 2 / 2
  | C1, ν, k, p => (ν - 2 * p - 1) * (ν + 2 * p + 2) * k ^ 2 / 2
  | D1, ν, k, p => (ν - 2 * p - 1) * (ν + 2 * p + 2) * k ^ 2 / 2
  | D2, ν, k, p => (ν - 2 * p - 2) * (ν + 2 * p + 3) * k ^ 2 / 2

/-- The coefficient `β_p` (DLMF 29.3.12, 29.3.13, 29.3.15, 29.3.17, 29.6.11, 29.6.26, 29.6.41,
29.6.56). -/
@[dlmf 29.3.E12, dlmf 29.3.E13, dlmf 29.3.E15, dlmf 29.3.E17, dlmf 29.6.E11, dlmf 29.6.E26,
  dlmf 29.6.E41, dlmf 29.6.E56]
def beta : LameRecurrence → ℝ → ℝ → ℕ → ℝ
  | A0, _, k, p => 4 * p ^ 2 * (2 - k ^ 2)
  | A1, ν, k, p =>
      if p = 0 then 2 - k ^ 2 + ν * (ν + 1) * k ^ 2 / 2 else (2 * p + 1) ^ 2 * (2 - k ^ 2)
  | B1, ν, k, p =>
      if p = 0 then 2 - k ^ 2 - ν * (ν + 1) * k ^ 2 / 2 else (2 * p + 1) ^ 2 * (2 - k ^ 2)
  | B2, _, k, p => (2 * p + 2) ^ 2 * (2 - k ^ 2)
  | C0, _, k, p => 4 * p ^ 2 * (2 - k ^ 2)
  | C1, ν, k, p =>
      if p = 0 then 2 - k ^ 2 + ν * (ν + 1) * k ^ 2 / 2 else (2 * p + 1) ^ 2 * (2 - k ^ 2)
  | D1, ν, k, p =>
      if p = 0 then 2 - k ^ 2 - ν * (ν + 1) * k ^ 2 / 2 else (2 * p + 1) ^ 2 * (2 - k ^ 2)
  | D2, _, k, p => (2 * p + 2) ^ 2 * (2 - k ^ 2)

/-- The coefficient `γ_p` (DLMF 29.3.12, 29.3.14, 29.3.16, 29.3.17, 29.6.11, 29.6.26, 29.6.41,
29.6.56). -/
@[dlmf 29.3.E12, dlmf 29.3.E14, dlmf 29.3.E16, dlmf 29.3.E17, dlmf 29.6.E11, dlmf 29.6.E26,
  dlmf 29.6.E41, dlmf 29.6.E56]
def gamma : LameRecurrence → ℝ → ℝ → ℕ → ℝ
  | A0, ν, k, p => (ν - 2 * p + 2) * (ν + 2 * p - 1) * k ^ 2 / 2
  | A1, ν, k, p => (ν - 2 * p + 1) * (ν + 2 * p) * k ^ 2 / 2
  | B1, ν, k, p => (ν - 2 * p + 1) * (ν + 2 * p) * k ^ 2 / 2
  | B2, ν, k, p => (ν - 2 * p) * (ν + 2 * p + 1) * k ^ 2 / 2
  | C0, ν, k, p => (ν - 2 * p + 1) * (ν + 2 * p) * k ^ 2 / 2
  | C1, ν, k, p => (ν - 2 * p) * (ν + 2 * p + 1) * k ^ 2 / 2
  | D1, ν, k, p => (ν - 2 * p) * (ν + 2 * p + 1) * k ^ 2 / 2
  | D2, ν, k, p => (ν - 2 * p - 1) * (ν + 2 * p + 2) * k ^ 2 / 2

/-- `c` satisfies the three-term recurrence `r` with eigenparameter `H` (DLMF 29.6.3–29.6.4 and
their analogues): `(β₀ - H)c₀ + α₀c₁ = 0` and
`γ_p c_{p-1} + (β_p - H)c_p + α_p c_{p+1} = 0` for `p ≥ 1`. The index `p` of `c` is the
position in the coefficient list (`c p = A_{2p}`, `A_{2p+1}`, `B_{2p+2}`, …). -/
def Satisfies (r : LameRecurrence) (ν k H : ℝ) (c : ℕ → ℝ) : Prop :=
  (r.beta ν k 0 - H) * c 0 + r.alpha ν k 0 * c 1 = 0 ∧
    ∀ p : ℕ, r.gamma ν k (p + 1) * c p + (r.beta ν k (p + 1) - H) * c (p + 1) +
      r.alpha ν k (p + 1) * c (p + 2) = 0

end LameRecurrence

/-- The left side of the continued-fraction equation 29.3.10 (finite):
`β_p - H - α_{p-1}γ_p/(β_{p-1} - H - ⋯ - α₀γ₁/(β₀ - H))`. -/
@[dlmf 29.3.E10]
def lameCFLeft (r : LameRecurrence) (ν k H : ℝ) : ℕ → ℝ
  | 0 => r.beta ν k 0 - H
  | p + 1 => r.beta ν k (p + 1) - H - r.alpha ν k p * r.gamma ν k (p + 1) / lameCFLeft r ν k H p

/-- The truncation at depth `d` of the right side of 29.3.10:
`α_pγ_{p+1}/(β_{p+1} - H - α_{p+1}γ_{p+2}/(β_{p+2} - H - ⋯))` with `d` partial denominators. -/
@[dlmf 29.3.E10]
def lameCFRight (r : LameRecurrence) (ν k H : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | p, d + 1 => r.alpha ν k p * r.gamma ν k (p + 1) /
      (r.beta ν k (p + 1) - H - lameCFRight r ν k H (p + 1) d)

/-! ### Fourier coefficients (§29.6) -/

/-- The cosine Fourier coefficient of a real function `w` in the variable `φ = π/2 - am(x, k)`
of 29.2.5, `(4/π) ∫₀^K w(x) cos(jφ(x)) ρ(x) dx` with `ρ = dn(x, k)` (`weighted`; this is
`(4/π) ∫₀^{π/2} w cos(jφ) dφ`, giving `A_j` in 29.6.1 and 29.6.16) or `ρ = 1` (giving `C_j` in
29.6.8 and 29.6.23, where `w/dn` is expanded). -/
def Real.lameCosCoeff (w : ℝ → ℝ) (k : ℝ) (weighted : Bool) (j : ℕ) : ℝ :=
  4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
    w x * Real.cos (j * Real.lamePhi x k) * (if weighted then Real.jacobiDnm x (k ^ 2) else 1)

/-- The sine Fourier coefficient `(4/π) ∫₀^K w(x) sin(jφ(x)) ρ(x) dx` (`ρ = dn` if `weighted`,
giving `B_j` in 29.6.31 and 29.6.46; `ρ = 1` giving `D_j` in 29.6.38 and 29.6.53). -/
def Real.lameSinCoeff (w : ℝ → ℝ) (k : ℝ) (weighted : Bool) (j : ℕ) : ℝ :=
  4 / π * ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
    w x * Real.sin (j * Real.lamePhi x k) * (if weighted then Real.jacobiDnm x (k ^ 2) else 1)

/-! ### Stability (§29.9) -/

/-- Lamé's equation 29.2.1 with parameters `k, h, ν` is stable if all its real solutions are
bounded on `ℝ` (DLMF §29.9). -/
@[dlmf 29.9]
def Real.IsLameStable (h ν k : ℝ) : Prop :=
  ∀ w : ℝ → ℝ, Real.IsLameSolution h ν k w → ∃ C, ∀ x, |w x| ≤ C

/-! ### Asymptotic coefficients (§29.7(i)) -/

/-- `κ = k(ν(ν+1))^{1/2}` (DLMF 29.7.2). -/
@[dlmf 29.7.E2]
def lameKappa (ν k : ℝ) : ℝ := k * Real.sqrt (ν * (ν + 1))

/-- The coefficient `τ₀ = (1 + k²)(1 + p²)/2³` (DLMF 29.7.3). -/
@[dlmf 29.7.E3]
def lameTau0 (p k : ℝ) : ℝ := (1 + k ^ 2) * (1 + p ^ 2) / 2 ^ 3

/-- The coefficient `τ₁ = p((1 + k²)²(p² + 3) - 4k²(p² + 5))/2⁶` (DLMF 29.7.4). -/
@[dlmf 29.7.E4]
def lameTau1 (p k : ℝ) : ℝ := p / 2 ^ 6 * ((1 + k ^ 2) ^ 2 * (p ^ 2 + 3) - 4 * k ^ 2 * (p ^ 2 + 5))

/-- The coefficient `τ₂ = (1 + k²)(1 - k²)²(5p⁴ + 34p² + 9)/2¹⁰` (DLMF 29.7.6). -/
@[dlmf 29.7.E6]
def lameTau2 (p k : ℝ) : ℝ := (1 + k ^ 2) * (1 - k ^ 2) ^ 2 * (5 * p ^ 4 + 34 * p ^ 2 + 9) / 2 ^ 10

/-- The coefficient `τ₃` of DLMF 29.7.7. -/
@[dlmf 29.7.E7]
def lameTau3 (p k : ℝ) : ℝ :=
  p / 2 ^ 14 * ((1 + k ^ 2) ^ 4 * (33 * p ^ 4 + 410 * p ^ 2 + 405) -
    24 * k ^ 2 * (1 + k ^ 2) ^ 2 * (7 * p ^ 4 + 90 * p ^ 2 + 95) +
    16 * k ^ 4 * (9 * p ^ 4 + 130 * p ^ 2 + 173))

/-- The coefficient `τ₄` of DLMF 29.7.8. -/
@[dlmf 29.7.E8]
def lameTau4 (p k : ℝ) : ℝ :=
  1 / 2 ^ 16 * ((1 + k ^ 2) ^ 5 * (63 * p ^ 6 + 1260 * p ^ 4 + 2943 * p ^ 2 + 486) -
    8 * k ^ 2 * (1 + k ^ 2) ^ 3 * (49 * p ^ 6 + 1010 * p ^ 4 + 2493 * p ^ 2 + 432) +
    16 * k ^ 4 * (1 + k ^ 2) * (35 * p ^ 6 + 760 * p ^ 4 + 2043 * p ^ 2 + 378))

/-- The coefficients of Lamé's equation 29.2.1 in the form of `Complex.linearODEValue`
(index `0`: coefficient of `w`, index `1`: coefficient of `w'`). -/
def lameODECoeff (h ν k : ℂ) : Fin 2 → ℂ → ℂ :=
  ![fun z => h - ν * (ν + 1) * k ^ 2 * jacobiSnk z k ^ 2, fun _ => 0]

end DLMF.Lame
