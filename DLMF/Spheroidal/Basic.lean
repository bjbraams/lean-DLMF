/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic
public import DLMF.Bessel.Basic
public import DLMF.Core.Framework

/-!
# Spheroidal wave functions: definitions (DLMF §§30.2–30.4, 30.6, 30.8, 30.11, 30.12)

This is the definitions file of the spheroidal area (DLMF Chapter 30). It contains

* the spheroidal differential equation 30.2.1 as predicates with genuine differentiability:
  `IsSpheroidalSolutionOn lam γ2 μ U w` (complex variable, open set `U` avoiding `±1`) and
  `IsSpheroidalSolutionReal lam γ2 μ f` (real variable on `(-1, 1)`), the Liouville normal
  form 30.2.2 (`IsSpheroidalLiouvilleSolution`), the form 30.2.4 in `ζ = γz`
  (`IsSpheroidalZetaSolution`) and the generalized equations 30.12.1, 30.12.2;
* the equation for the entire factor `g` of a bounded solution `(1 - z²)^{m/2} g(z)`
  (`IsSpheroidalFactor m γ2 lam g`, DLMF §30.3(i)), the spectrum `spheroidalSpectrum m γ2`, and
  the eigenvalue `spheroidalEigenvalue n m γ2 = λ^m_n(γ²)`, the `(n - m)`-th smallest element of
  the spectrum (DLMF 30.3.1);
* the entire factor `spheroidalPsFactor n m γ2`, normalized by 30.4.1 and the sign convention of
  §30.4(i), and the angular functions of the first kind `spheroidalPs n m x γ2 = 𝖯s^m_n(x, γ²)`
  (§30.4) and `spheroidalPsC n m z γ2 = 𝑃s^m_n(z, γ²)` (§30.6);
* the coefficients of the continued-fraction equations 30.3.6 and 30.3.7, the recurrence
  coefficients `A_k, B_k, C_k` of 30.8.3, the forward solution of 30.8.4 used in §30.8(ii) and
  the constant `C'` of 30.8.11;
* the functions `ψ_k^{(j)}(z) = (π/(2z))^{1/2} 𝒞^{(j)}_{k+1/2}(z)` of 30.11.1–30.11.2
  (`spheroidalPsi`; for `j = 1` the entire `j_k`, `DLMF.sphericalJ` from `DLMF.Core`);
* the Taylor coefficients `ℓ_{2k}` of 30.3.8 and the coefficients of the large-`γ` expansions
  30.9.1–30.9.6;
* the expansion coefficients `c_n` of 30.4.8.

The definitions that need the Ferrers functions (`a^m_{n,k}(γ²)`, `A^{±m}_n(γ²)`, `𝖰s`, `𝑄s`,
the radial functions `S^{m(j)}_n` and Flammer's functions of 30.1.1) are in
`DLMF.Spheroidal.FerrersDefs`.

## Design notes

* `γ²` is a real parameter (DLMF §30.1), written `γ2 : ℝ`. Prolate: `γ2 > 0`, oblate:
  `γ2 < 0`. The degree comes before the order (`n m`, as for the project's `ferrersP ν μ x`),
  followed by DLMF's arguments `(x, γ²)`.
* **Eigenvalues (choice flagged).** DLMF §30.3(i) characterizes `Ps^m_n` as the solutions of
  30.2.1 with `μ = m` of the form `(1-x²)^{m/2} g(x)`, `g` entire; such solutions exist only for
  the eigenvalues `λ^m_n(γ²)`, `n = m, m+1, …`, ordered by 30.3.1. Here
  `spheroidalSpectrum m γ2` is the set of real `λ` for which the transformed equation
  `(1-z²)g'' - 2(m+1)zg' + (λ - m(m+1) + γ²(1-z²))g = 0` has a nonzero entire solution, and
  `spheroidalEigenvalue n m γ2` is the element of the spectrum with exactly `n - m` smaller
  elements (junk `0` if there is none). The admitted theorem `exists_spheroidalEigenvalue`
  (Sturm–Liouville theory) asserts that it exists; the ordering 30.3.1 is then proved.
* **Eigenfunctions (choice flagged).** `spheroidalPsFactor n m γ2` is the entire function `g`
  with the eigenvalue `λ^m_n(γ²)`, real on `ℝ`, with `∫_{-1}^1 (1-x²)^m g(x)² dx` given by
  30.4.1 and the sign of `g(0)` (`n - m` even) or `g'(0)` (`n - m` odd) of §30.4(i); it is
  defined by choice, with existence and uniqueness admitted in
  `existsUnique_isSpheroidalPsFactor` (simplicity of the eigenvalues). Since
  `(1 - x²)^{m/2}` has derivative `0` at `x = 0`, the signs of `g(0)`, `g'(0)` are those of
  `𝖯s(0)`, `𝖯s'(0)`.
* `𝑃s^m_n(z, γ²) = (-1)^m (z-1)^{m/2} (z+1)^{m/2} g(z)` with principal powers: this is real on
  `(1, ∞)`, analytic on `ℂ ∖ (-∞, 1]`, and has the boundary values 30.6.4; at `γ = 0` it is
  `P^m_n(z) = (z²-1)^{m/2} dᵐP_n/dzᵐ` (DLMF 14.6.5, 30.6.2).
* Series in the definitions are `tsum`s (totalized); their convergence is stated separately.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real Classical

namespace DLMF.Spheroidal

/-- `dif_pos` without the deprecation. -/
private theorem s30_dif_pos {c : Prop} [Decidable c] (h : c) {α : Sort*} {t : c → α}
    {e : ¬c → α} : dite c t e = t h := by simp [h]

/-! ### The spheroidal differential equation (§30.2) -/

/-- **The spheroidal differential equation** (DLMF 30.2.1)
`d/dz((1-z²) dw/dz) + (λ + γ²(1-z²) - μ²/(1-z²)) w = 0` on a set `U` (to be taken open and
avoiding `±1`), with complex parameters: `w` is differentiable at every point of `U` and
`(1-z²) w'(z)` has derivative `-(λ + γ²(1-z²) - μ²/(1-z²)) w(z)` there. -/
@[dlmf 30.2.E1]
structure IsSpheroidalSolutionOn (lam γ2 μ : ℂ) (U : Set ℂ) (w : ℂ → ℂ) : Prop where
  /-- `w` is complex differentiable on `U`. -/
  differentiableAt : ∀ z ∈ U, DifferentiableAt ℂ w z
  /-- The equation 30.2.1 in divergence form. -/
  hasDerivAt : ∀ z ∈ U, HasDerivAt (fun t => (1 - t ^ 2) * deriv w t)
    (-(lam + γ2 * (1 - z ^ 2) - μ ^ 2 / (1 - z ^ 2)) * w z) z

/-- **The spheroidal differential equation on `(-1, 1)`** (DLMF 30.2.1 with `z = x` real and
real parameters), for real-valued `f`: `f` is differentiable on `(-1, 1)` and `(1-x²) f'(x)` has
derivative `-(λ + γ²(1-x²) - μ²/(1-x²)) f(x)` there. -/
@[dlmf 30.2.E1]
structure IsSpheroidalSolutionReal (lam γ2 μ : ℝ) (f : ℝ → ℝ) : Prop where
  /-- `f` is differentiable on `(-1, 1)`. -/
  differentiableAt : ∀ x ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ f x
  /-- The equation 30.2.1 in divergence form. -/
  hasDerivAt : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun t => (1 - t ^ 2) * deriv f t)
    (-(lam + γ2 * (1 - x ^ 2) - μ ^ 2 / (1 - x ^ 2)) * f x) x

/-- **The Liouville normal form** (DLMF 30.2.2)
`g'' + (λ + 1/4 + γ² sin²t - (μ² - 1/4)/sin²t) g = 0` on a set `T` of complex `t` (to be taken
open and free of zeros of `sin t`). -/
@[dlmf 30.2.E2]
structure IsSpheroidalLiouvilleSolution (lam γ2 μ : ℂ) (T : Set ℂ) (g : ℂ → ℂ) : Prop where
  /-- `g` is complex differentiable on `T`. -/
  differentiableAt : ∀ t ∈ T, DifferentiableAt ℂ g t
  /-- The equation 30.2.2. -/
  hasDerivAt : ∀ t ∈ T, HasDerivAt (deriv g)
    (-(lam + 1 / 4 + γ2 * Complex.sin t ^ 2 - (μ ^ 2 - 1 / 4) / Complex.sin t ^ 2) * g t) t

/-- **The spheroidal equation in the variable `ζ = γz`** (DLMF 30.2.4)
`(ζ² - γ²) w'' + 2ζ w' + (ζ² - λ - γ² - γ²μ²/(ζ² - γ²)) w = 0` on a set `V` (to be taken open and
avoiding `±γ`); `γ2` stands for `γ²`. -/
@[dlmf 30.2.E4]
structure IsSpheroidalZetaSolution (lam γ2 μ : ℂ) (V : Set ℂ) (w : ℂ → ℂ) : Prop where
  /-- `w` is complex differentiable on `V`. -/
  differentiableAt : ∀ ζ ∈ V, DifferentiableAt ℂ w ζ
  /-- `w'` is complex differentiable on `V`. -/
  differentiableAt_deriv : ∀ ζ ∈ V, DifferentiableAt ℂ (deriv w) ζ
  /-- The equation 30.2.4. -/
  ode : ∀ ζ ∈ V, (ζ ^ 2 - γ2) * deriv (deriv w) ζ + 2 * ζ * deriv w ζ +
    (ζ ^ 2 - lam - γ2 - γ2 * μ ^ 2 / (ζ ^ 2 - γ2)) * w ζ = 0

/-- **Generalized spheroidal wave equation** (DLMF 30.12.1)
`d/dz((1-z²) w') + (λ + αz + γ²(1-z²) - μ²/(1-z²)) w = 0` on `U`; Coulomb spheroidal
functions are solutions. -/
@[dlmf 30.12.E1]
structure IsGenSpheroidalSolutionOn (lam α γ2 μ : ℂ) (U : Set ℂ) (w : ℂ → ℂ) : Prop where
  /-- `w` is complex differentiable on `U`. -/
  differentiableAt : ∀ z ∈ U, DifferentiableAt ℂ w z
  /-- The equation 30.12.1 in divergence form. -/
  hasDerivAt : ∀ z ∈ U, HasDerivAt (fun t => (1 - t ^ 2) * deriv w t)
    (-(lam + α * z + γ2 * (1 - z ^ 2) - μ ^ 2 / (1 - z ^ 2)) * w z) z

/-- **The second generalization** (DLMF 30.12.2)
`d/dz((1-z²) w') + (λ + γ²(1-z²) - α(α+1)/z² - μ²/(1-z²)) w = 0` on `U` (to be taken open and
avoiding `0, ±1`). -/
@[dlmf 30.12.E2]
structure IsSpheroidalSolutionOn₂ (lam α γ2 μ : ℂ) (U : Set ℂ) (w : ℂ → ℂ) : Prop where
  /-- `w` is complex differentiable on `U`. -/
  differentiableAt : ∀ z ∈ U, DifferentiableAt ℂ w z
  /-- The equation 30.12.2 in divergence form. -/
  hasDerivAt : ∀ z ∈ U, HasDerivAt (fun t => (1 - t ^ 2) * deriv w t)
    (-(lam + γ2 * (1 - z ^ 2) - α * (α + 1) / z ^ 2 - μ ^ 2 / (1 - z ^ 2)) * w z) z

/-! ### Eigenvalues (§30.3) -/

/-- **The equation of the entire factor** (DLMF §30.3(i)): `w = (1-z²)^{m/2} g(z)` solves 30.2.1
with `μ = m` if and only if `g` solves
`(1-z²) g'' - 2(m+1) z g' + (λ - m(m+1) + γ²(1-z²)) g = 0`; here `g` is entire. Its power-series
coefficients satisfy the recurrence 30.4.5. -/
@[dlmf 30.3.i]
structure IsSpheroidalFactor (m : ℕ) (γ2 lam : ℝ) (g : ℂ → ℂ) : Prop where
  /-- `g` is entire. -/
  differentiable : Differentiable ℂ g
  /-- The transformed equation. -/
  ode : ∀ z : ℂ, (1 - z ^ 2) * deriv (deriv g) z - 2 * ((m : ℂ) + 1) * z * deriv g z +
    ((lam : ℂ) - m * ((m : ℂ) + 1) + γ2 * (1 - z ^ 2)) * g z = 0

/-- **The spectrum** of the spheroidal equation of order `m` (DLMF §30.3(i)): the real `λ` for
which 30.2.1 with `μ = m` has a nonzero solution `(1-x²)^{m/2} g(x)` with `g` entire. -/
@[dlmf 30.3.i]
def spheroidalSpectrum (m : ℕ) (γ2 : ℝ) : Set ℝ :=
  {lam | ∃ g : ℂ → ℂ, IsSpheroidalFactor m γ2 lam g ∧ g ≠ 0}

/-- **The eigenvalue** `λ^m_n(γ²)` (DLMF §30.3(i), 30.3.1), for real `γ²` and `n ≥ m`: the element
of `spheroidalSpectrum m γ2` with exactly `n - m` smaller elements (junk `0` if there is none;
the admitted `exists_spheroidalEigenvalue` asserts existence for `m ≤ n`). -/
@[dlmf 30.3.i]
def spheroidalEigenvalue (n m : ℕ) (γ2 : ℝ) : ℝ :=
  if h : ∃ lam ∈ spheroidalSpectrum m γ2,
      (spheroidalSpectrum m γ2 ∩ Iio lam).encard = ((n - m : ℕ) : ℕ∞) then h.choose else 0

/-- **Existence of the eigenvalues** (DLMF §30.3(i)): for `m ≤ n` the spectrum has an element with
exactly `n - m` smaller elements. Flagged existence theorem (admitted): the spectrum of the
singular Sturm–Liouville problem on `(-1, 1)` is an unbounded increasing sequence of simple
eigenvalues. -/
@[dlmf 30.3.i]
theorem exists_spheroidalEigenvalue {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∃ lam ∈ spheroidalSpectrum m γ2,
      (spheroidalSpectrum m γ2 ∩ Iio lam).encard = ((n - m : ℕ) : ℕ∞) := by
  sorry

/-- The defining property of `λ^m_n(γ²)` (DLMF §30.3(i)), from `exists_spheroidalEigenvalue`. -/
theorem spheroidalEigenvalue_spec {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    spheroidalEigenvalue n m γ2 ∈ spheroidalSpectrum m γ2 ∧
      (spheroidalSpectrum m γ2 ∩ Iio (spheroidalEigenvalue n m γ2)).encard =
        ((n - m : ℕ) : ℕ∞) := by
  have h := exists_spheroidalEigenvalue hmn γ2
  simp only [spheroidalEigenvalue, s30_dif_pos h]
  exact h.choose_spec

/-! ### Functions of the first kind (§30.4, §30.6) -/

/-- **Normalized entire factor of `𝖯s^m_n`** (DLMF §30.4(i)): `g` is an entire solution of the
factor equation with `λ = λ^m_n(γ²)`, real on the real axis, normalized by 30.4.1
(`∫_{-1}^1 (1-x²)^m g(x)² dx = 2(n+m)!/((2n+1)(n-m)!)`), with `(-1)^{(n+m)/2} g(0) > 0` for
`n - m` even and `(-1)^{(n+m-1)/2} g'(0) > 0` for `n - m` odd. -/
@[dlmf 30.4.E1]
structure IsSpheroidalPsFactor (n m : ℕ) (γ2 : ℝ) (g : ℂ → ℂ) : Prop where
  /-- `g` solves the factor equation with the eigenvalue `λ^m_n(γ²)`. -/
  factor : IsSpheroidalFactor m γ2 (spheroidalEigenvalue n m γ2) g
  /-- `g` is real on the real axis. -/
  real : ∀ x : ℝ, (g x).im = 0
  /-- The normalization 30.4.1. -/
  normalized : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ m * (g x).re ^ 2 =
    2 / (2 * n + 1) * (((n + m).factorial : ℝ) / (n - m).factorial)
  /-- The sign of `𝖯s(0)` for `n - m` even. -/
  sign_even : Even (n - m) → 0 < (-1 : ℝ) ^ ((n + m) / 2) * (g 0).re
  /-- The sign of `𝖯s'(0)` for `n - m` odd. -/
  sign_odd : Odd (n - m) → 0 < (-1 : ℝ) ^ ((n + m - 1) / 2) * (deriv g 0).re

/-- **Existence and uniqueness of the normalized eigenfunction** (DLMF §30.4(i)). Flagged
existence theorem (admitted): the eigenvalues are simple, the eigenfunction can be taken real,
and an even (odd) nonzero solution has `g(0) ≠ 0` (`g'(0) ≠ 0`). -/
@[dlmf 30.4.i]
theorem existsUnique_isSpheroidalPsFactor {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    ∃! g, IsSpheroidalPsFactor n m γ2 g := by
  sorry

/-- The entire factor `g` of `𝖯s^m_n(x, γ²) = (1-x²)^{m/2} g(x)` (DLMF §30.3(i), §30.4(i)),
defined by choice (junk `0` if it did not exist). -/
def spheroidalPsFactor (n m : ℕ) (γ2 : ℝ) : ℂ → ℂ :=
  if h : ∃ g, IsSpheroidalPsFactor n m γ2 g then h.choose else 0

/-- The defining property of `spheroidalPsFactor`, from `existsUnique_isSpheroidalPsFactor`. -/
theorem spheroidalPsFactor_spec {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    IsSpheroidalPsFactor n m γ2 (spheroidalPsFactor n m γ2) := by
  have h := (existsUnique_isSpheroidalPsFactor hmn γ2).exists
  simp only [spheroidalPsFactor, s30_dif_pos h]
  exact h.choose_spec

/-- **The spheroidal wave function of the first kind** `𝖯s^m_n(x, γ²)` (DLMF §30.4(i)):
`(1-x²)^{m/2} g(x)` with `g = spheroidalPsFactor n m γ2`; meaningful for `-1 ≤ x ≤ 1`. Prolate
angular function for `γ² > 0`, oblate for `γ² < 0`. -/
@[dlmf 30.4.i]
def spheroidalPs (n m : ℕ) (x γ2 : ℝ) : ℝ :=
  (1 - x ^ 2) ^ ((m : ℝ) / 2) * (spheroidalPsFactor n m γ2 x).re

/-- **The spheroidal wave function of the first kind of complex argument** `𝑃s^m_n(z, γ²)`
(DLMF 30.6.1): `(-1)^m (z-1)^{m/2} (z+1)^{m/2} g(z)` with principal powers and
`g = spheroidalPsFactor n m γ2`; real on `(1, ∞)` and analytic on `ℂ ∖ (-∞, 1]`. -/
@[dlmf 30.6.E1]
def spheroidalPsC (n m : ℕ) (z : ℂ) (γ2 : ℝ) : ℂ :=
  (-1) ^ m * (z - 1) ^ ((m : ℂ) / 2) * (z + 1) ^ ((m : ℂ) / 2) * spheroidalPsFactor n m γ2 z

/-- **Expansion coefficients** `c_n` of a function `f` in the functions `𝖯s^m_n(x, γ²)`
(DLMF 30.4.8): `c_n = (n + 1/2) (n-m)!/(n+m)! ∫_{-1}^1 f(t) 𝖯s^m_n(t, γ²) dt`. -/
@[dlmf 30.4.E8]
def spheroidalExpansionCoeff (m : ℕ) (γ2 : ℝ) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1 / 2) * (((n - m).factorial : ℝ) / (n + m).factorial) *
    ∫ t in (-1 : ℝ)..1, f t * spheroidalPs n m t γ2

/-! ### Coefficients of the continued fractions and recurrences (§§30.3, 30.8) -/

/-- `α_k = -(k+1)(k+2)` (DLMF 30.3.6), the coefficients of the power-series recurrence 30.4.5. -/
@[dlmf 30.3.E6]
def spheroidalCFAlpha (_m : ℕ) (_γ2 : ℝ) (k : ℕ) : ℝ := -((k : ℝ) + 1) * ((k : ℝ) + 2)

/-- `β_k = (m+k)(m+k+1) - γ²` (DLMF 30.3.6). -/
@[dlmf 30.3.E6]
def spheroidalCFBeta (m : ℕ) (γ2 : ℝ) (k : ℕ) : ℝ := ((m : ℝ) + k) * ((m : ℝ) + k + 1) - γ2

/-- `γ_k = γ²` (DLMF 30.3.6). -/
@[dlmf 30.3.E6]
def spheroidalCFGamma (_m : ℕ) (γ2 : ℝ) (_k : ℕ) : ℝ := γ2

/-- `α_k = γ² (k+2m+1)(k+2m+2)/((2k+2m+3)(2k+2m+5))` (DLMF 30.3.7). -/
@[dlmf 30.3.E7]
def spheroidalCFAlphaAlt (m : ℕ) (γ2 : ℝ) (k : ℕ) : ℝ :=
  γ2 * (((k : ℝ) + 2 * m + 1) * ((k : ℝ) + 2 * m + 2)) /
    ((2 * (k : ℝ) + 2 * m + 3) * (2 * (k : ℝ) + 2 * m + 5))

/-- `β_k = (k+m)(k+m+1) - 2γ² ((k+m)(k+m+1) - 1 + m²)/((2k+2m-1)(2k+2m+3))` (DLMF 30.3.7). -/
@[dlmf 30.3.E7]
def spheroidalCFBetaAlt (m : ℕ) (γ2 : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + m) * ((k : ℝ) + m + 1) - 2 * γ2 * (((k : ℝ) + m) * ((k : ℝ) + m + 1) - 1 + m ^ 2) /
    ((2 * (k : ℝ) + 2 * m - 1) * (2 * (k : ℝ) + 2 * m + 3))

/-- `γ_k = γ² (k-1)k/((2k+2m-3)(2k+2m-1))` (DLMF 30.3.7). -/
@[dlmf 30.3.E7]
def spheroidalCFGammaAlt (m : ℕ) (γ2 : ℝ) (k : ℕ) : ℝ :=
  γ2 * (((k : ℝ) - 1) * k) / ((2 * (k : ℝ) + 2 * m - 3) * (2 * (k : ℝ) + 2 * m - 1))

/-- `A_k = -γ² (n-m+2k-1)(n-m+2k)/((2n+4k-3)(2n+4k-1))` (DLMF 30.8.3), `k ∈ ℤ`. -/
@[dlmf 30.8.E3]
def spheroidalRecA (n m : ℕ) (γ2 : ℝ) (k : ℤ) : ℝ :=
  -γ2 * (((n : ℝ) - m + 2 * k - 1) * ((n : ℝ) - m + 2 * k)) /
    ((2 * (n : ℝ) + 4 * k - 3) * (2 * (n : ℝ) + 4 * k - 1))

/-- `B_k = (n+2k)(n+2k+1) - 2γ² ((n+2k)(n+2k+1) - 1 + m²)/((2n+4k-1)(2n+4k+3))`
(DLMF 30.8.3), `k ∈ ℤ`. -/
@[dlmf 30.8.E3]
def spheroidalRecB (n m : ℕ) (γ2 : ℝ) (k : ℤ) : ℝ :=
  ((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) -
    2 * γ2 * (((n : ℝ) + 2 * k) * ((n : ℝ) + 2 * k + 1) - 1 + m ^ 2) /
      ((2 * (n : ℝ) + 4 * k - 1) * (2 * (n : ℝ) + 4 * k + 3))

/-- `C_k = -γ² (n+m+2k+1)(n+m+2k+2)/((2n+4k+3)(2n+4k+5))` (DLMF 30.8.3), `k ∈ ℤ`. -/
@[dlmf 30.8.E3]
def spheroidalRecC (n m : ℕ) (γ2 : ℝ) (k : ℤ) : ℝ :=
  -γ2 * (((n : ℝ) + m + 2 * k + 1) * ((n : ℝ) + m + 2 * k + 2)) /
    ((2 * (n : ℝ) + 4 * k + 3) * (2 * (n : ℝ) + 4 * k + 5))

/-- The forward solution of the recurrence 30.8.4 used in DLMF §30.8(ii): with
`N = ⌊(n+m)/2⌋`, `spheroidalFwd n m γ2 j = f_{j-N-1}` where `f_{-N-1} = 0`, `f_{-N} = 1` and
`A_k f_{k-1} + (B_k - λ^m_n(γ²)) f_k + C_k f_{k+1} = 0`. -/
@[dlmf 30.8.ii]
def spheroidalFwd (n m : ℕ) (γ2 : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | j + 2 =>
    -(spheroidalRecA n m γ2 (-(((n + m) / 2 : ℕ) : ℤ) + j) * spheroidalFwd n m γ2 j +
        (spheroidalRecB n m γ2 (-(((n + m) / 2 : ℕ) : ℤ) + j) - spheroidalEigenvalue n m γ2) *
          spheroidalFwd n m γ2 (j + 1)) /
      spheroidalRecC n m γ2 (-(((n + m) / 2 : ℕ) : ℤ) + j)

/-- The constant `C'` of DLMF 30.8.11: `γ²/(4m²-1)` for `n - m` even and
`-γ²/((2m-1)(2m-3))` for `n - m` odd. -/
@[dlmf 30.8.E11]
def spheroidalCPrime (n m : ℕ) (γ2 : ℝ) : ℝ :=
  if Even (n - m) then γ2 / (4 * (m : ℝ) ^ 2 - 1) else -γ2 / ((2 * (m : ℝ) - 1) * (2 * m - 3))

/-! ### Power-series and asymptotic coefficients of the eigenvalues (§§30.3(iv), 30.9) -/

/-- The coefficient `ℓ_{2k}` of `γ^{2k}` in the expansion 30.3.8 of `λ^m_n(γ²)`: the `k`-th
Taylor coefficient at `0` of `γ² ↦ λ^m_n(γ²)`. -/
@[dlmf 30.3.E8]
def spheroidalEll (n m k : ℕ) : ℝ :=
  iteratedDeriv k (fun t => spheroidalEigenvalue n m t) 0 / k.factorial

/-- The auxiliary quantity `A` of DLMF 30.3.12 (entering `ℓ_8`, 30.3.11). -/
@[dlmf 30.3.E12]
def spheroidalEllA (n m : ℕ) : ℝ :=
  let a : ℝ := n
  let b : ℝ := m
  (a - b - 1) * (a - b) * (a + b - 1) * (a + b) /
      ((2 * a - 5) ^ 2 * (2 * a - 3) * (2 * a - 1) ^ 7 * (2 * a + 1) * (2 * a + 3) ^ 2) -
    (a - b + 1) * (a - b + 2) * (a + b + 1) * (a + b + 2) /
      ((2 * a - 1) ^ 2 * (2 * a + 1) * (2 * a + 3) ^ 7 * (2 * a + 5) * (2 * a + 7) ^ 2)

/-- The auxiliary quantity `B` of DLMF 30.3.12. -/
@[dlmf 30.3.E12]
def spheroidalEllB (n m : ℕ) : ℝ :=
  let a : ℝ := n
  let b : ℝ := m
  (a - b - 3) * (a - b - 2) * (a - b - 1) * (a - b) * (a + b - 3) * (a + b - 2) * (a + b - 1) *
        (a + b) /
      ((2 * a - 7) * (2 * a - 5) ^ 2 * (2 * a - 3) ^ 3 * (2 * a - 1) ^ 4 * (2 * a + 1)) -
    (a - b + 1) * (a - b + 2) * (a - b + 3) * (a - b + 4) * (a + b + 1) * (a + b + 2) *
        (a + b + 3) * (a + b + 4) /
      ((2 * a + 1) * (2 * a + 3) ^ 4 * (2 * a + 5) ^ 3 * (2 * a + 7) ^ 2 * (2 * a + 9))

/-- The auxiliary quantity `C` of DLMF 30.3.12. -/
@[dlmf 30.3.E12]
def spheroidalEllC (n m : ℕ) : ℝ :=
  let a : ℝ := n
  let b : ℝ := m
  (a - b + 1) ^ 2 * (a - b + 2) ^ 2 * (a + b + 1) ^ 2 * (a + b + 2) ^ 2 /
      ((2 * a + 1) ^ 2 * (2 * a + 3) ^ 7 * (2 * a + 5) ^ 2) -
    (a - b - 1) ^ 2 * (a - b) ^ 2 * (a + b - 1) ^ 2 * (a + b) ^ 2 /
      ((2 * a - 3) ^ 2 * (2 * a - 1) ^ 7 * (2 * a + 1) ^ 2)

/-- The auxiliary quantity `D` of DLMF 30.3.12. -/
@[dlmf 30.3.E12]
def spheroidalEllD (n m : ℕ) : ℝ :=
  let a : ℝ := n
  let b : ℝ := m
  (a - b - 1) * (a - b) * (a - b + 1) * (a - b + 2) * (a + b - 1) * (a + b) * (a + b + 1) *
      (a + b + 2) /
    ((2 * a - 3) * (2 * a - 1) ^ 4 * (2 * a + 1) ^ 2 * (2 * a + 3) ^ 4 * (2 * a + 5))

/-- The coefficients `β_0, …, β_5` of the prolate expansion 30.9.1 (DLMF 30.9.2, 30.9.3), with
`q = 2(n-m)+1`; `0` for `j ≥ 6` (not given by DLMF). -/
@[dlmf 30.9.E2]
def spheroidalProlateBeta (n m : ℕ) (j : ℕ) : ℝ :=
  let q : ℝ := 2 * ((n : ℝ) - m) + 1
  let m2 : ℝ := (m : ℝ) ^ 2
  match j with
  | 0 => (8 * m2 - q ^ 2 - 5) / 8
  | 1 => (-q ^ 3 - 11 * q + 32 * m2 * q) / 2 ^ 6
  | 2 => (-5 * (q ^ 4 + 26 * q ^ 2 + 21) + 384 * m2 * (q ^ 2 + 1)) / 2 ^ 10
  | 3 => (-33 * q ^ 5 - 1594 * q ^ 3 - 5621 * q + 128 * m2 * (37 * q ^ 3 + 167 * q) -
      2048 * m2 ^ 2 * q) / 2 ^ 14
  | 4 => (-63 * q ^ 6 - 4940 * q ^ 4 - 43327 * q ^ 2 - 22470 +
      128 * m2 * (115 * q ^ 4 + 1310 * q ^ 2 + 735) - 24576 * m2 ^ 2 * (q ^ 2 + 1)) / 2 ^ 16
  | 5 => (-527 * q ^ 7 - 61529 * q ^ 5 - 1043961 * q ^ 3 - 2241599 * q +
      32 * m2 * (5739 * q ^ 5 + 127550 * q ^ 3 + 298951 * q) -
      2048 * m2 ^ 2 * (355 * q ^ 3 + 1505 * q) + 65536 * m2 ^ 3 * q) / 2 ^ 20
  | _ => 0

/-- The parameter `q` of the oblate expansion 30.9.4: `n + 1` for `n - m` even, `n` for `n - m`
odd. -/
@[dlmf 30.9.ii]
def spheroidalOblateQ (n m : ℕ) : ℝ := if Even (n - m) then (n : ℝ) + 1 else n

/-- The coefficients `c_0, …, c_5` of the oblate expansion 30.9.4 (DLMF 30.9.5, 30.9.6); `0` for
`j ≥ 6` (not given by DLMF). -/
@[dlmf 30.9.E5]
def spheroidalOblateC (n m : ℕ) (j : ℕ) : ℝ :=
  let q : ℝ := spheroidalOblateQ n m
  let m2 : ℝ := (m : ℝ) ^ 2
  match j with
  | 0 => (-q ^ 2 - 1 + m2) / 2
  | 1 => (-q ^ 3 - q + m2 * q) / 8
  | 2 => (-5 * q ^ 4 - 10 * q ^ 2 - 1 + 2 * m2 * (3 * q ^ 2 + 1) - m2 ^ 2) / 2 ^ 6
  | 3 => (-33 * q ^ 5 - 114 * q ^ 3 - 37 * q + 2 * m2 * (23 * q ^ 3 + 25 * q) -
      13 * m2 ^ 2 * q) / 2 ^ 9
  | 4 => (-63 * q ^ 6 - 340 * q ^ 4 - 239 * q ^ 2 - 14 + 10 * m2 * (10 * q ^ 4 + 23 * q ^ 2 + 3) -
      3 * m2 ^ 2 * (13 * q ^ 2 + 6) + 2 * m2 ^ 3) / 2 ^ 10
  | 5 => (-527 * q ^ 7 - 4139 * q ^ 5 - 5221 * q ^ 3 - 1009 * q +
      m2 * (939 * q ^ 5 + 3750 * q ^ 3 + 1591 * q) - m2 ^ 2 * (465 * q ^ 3 + 635 * q) +
      53 * m2 ^ 3 * q) / 2 ^ 13
  | _ => 0

/-! ### Radial building blocks (§30.11(i)) -/

/-- The cylinder functions `𝒞^{(1)}_ν = J_ν`, `𝒞^{(2)}_ν = Y_ν`,
`𝒞^{(3)}_ν = H^{(1)}_ν = J_ν + iY_ν`, `𝒞^{(4)}_ν = H^{(2)}_ν = J_ν - iY_ν` of DLMF 30.11.2
(junk `0` for `j ∉ {1, 2, 3, 4}`). -/
@[dlmf 30.11.E2]
def spheroidalCylinder (j : ℕ) (ν z : ℂ) : ℂ :=
  match j with
  | 1 => besselJ ν z
  | 2 => DLMF.Bessel.besselY ν z
  | 3 => besselJ ν z + I * DLMF.Bessel.besselY ν z
  | 4 => besselJ ν z - I * DLMF.Bessel.besselY ν z
  | _ => 0

/-- `ψ_k^{(j)}(z) = (π/(2z))^{1/2} 𝒞^{(j)}_{k+1/2}(z)`, `j = 1, 2, 3, 4` (DLMF 30.11.1), with the
principal square root; these are the spherical Bessel functions `j_k`, `y_k`, `h_k^{(1)}`,
`h_k^{(2)}` of DLMF 10.47.3–10.47.4. For `j = 1` the entire function `j_k` is used (the project's
`DLMF.sphericalJ`), since DLMF allows every `z ≠ 0` in 30.11.3 for `j = 1`; it agrees with the
principal-branch formula off `(-∞, 0]` (`spheroidalPsi_one_eq`), where the formula would change
sign. -/
@[dlmf 30.11.E1]
def spheroidalPsi (j k : ℕ) (z : ℂ) : ℂ :=
  if j = 1 then DLMF.sphericalJ k z
  else ((π : ℂ) / (2 * z)) ^ (1 / 2 : ℂ) * spheroidalCylinder j ((k : ℂ) + 1 / 2) z

end DLMF.Spheroidal
