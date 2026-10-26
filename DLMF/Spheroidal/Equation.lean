/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.Basic
public import DLMF.Legendre.Ferrers
public import DLMF.Core.Framework

/-!
# The spheroidal differential equation (DLMF §30.2, §30.3(i), §30.12)

Statement acquisition from NIST DLMF (version 1.2.8), checked 2026-10-26. Admitted statements
are not completed proofs; see `DLMF30Acquisition.md`.

* §30.2(i): the singularities of 30.2.1 (regular at `±1` with exponents `±μ/2`, irregular of
  rank 1 at `∞`), stated through the indicial equation at `z = 1`;
* §30.2(ii): the Liouville normal form 30.2.2 under 30.2.3, and the form 30.2.4 in `ζ = γz`;
* §30.2(iii): the special cases `γ = 0` (associated Legendre equation 14.2.2, spherical Bessel
  equation 10.47.1) and `μ² = 1/4` (Mathieu's equation 28.2.1);
* §30.3(i): `(1-z²)^{m/2} g(z)` solves 30.2.1 with `μ = m` iff `g` solves the factor equation;
* §30.12: the generalized equations 30.12.1 and 30.12.2 reduce to 30.2.1 at `α = 0` (proved).
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Spheroidal

/-! ### §30.2(i) Singularities -/

/-- **Regular singularity at `z = 1`** (DLMF §30.2(i)): multiplying 30.2.1 by `(1-z²)` gives
`(1-z²)² w'' - 2z(1-z²) w' + (λ(1-z²) + γ²(1-z²)² - μ²) w = 0`, whose indicial equation at
`z = 1` (with `1 - z² = (1-z)(1+z)`, leading factor `4(z-1)²`) is `4ρ² - μ² = 0`, so the exponents
are `±μ/2` (proved: the roots of the indicial polynomial). -/
@[dlmf 30.2.i]
theorem spheroidal_indicial_exponents (μ ρ : ℂ) :
    4 * ρ * (ρ - 1) + 4 * ρ - μ ^ 2 = 0 ↔ ρ = μ / 2 ∨ ρ = -(μ / 2) := by
  constructor
  · intro h
    have h' : (ρ - μ / 2) * (ρ + μ / 2) = 0 := by linear_combination h / 4
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  · rintro (rfl | rfl) <;> ring

/-- **Irregular singularity at infinity** (DLMF §30.2(i)): for `γ ≠ 0`, 30.2.1 has an irregular
singular point of rank 1 at `z = ∞`: every nonzero solution on a neighbourhood of `∞` grows or
decays like `exp(±iγz) z^{ρ}` there, so `w(z) e^{∓iγz}` has at most polynomial behaviour along
suitable rays. Stated (admitted) as the existence of the two formal exponents: there are
solutions on `{|z| > 1} ∖ (-∞, -1]` with `w(z) ∼ e^{±iγz}/z` as `z → +∞` along the reals. -/
@[dlmf 30.2.i]
theorem spheroidal_irregular_infinity (lam μ γ : ℂ) (hγ : γ ≠ 0) :
    ∀ s : ℂ, s = 1 ∨ s = -1 → ∃ w : ℂ → ℂ,
      IsSpheroidalSolutionOn lam (γ ^ 2) μ {z : ℂ | 1 < ‖z‖ ∧ z + 1 ∈ slitPlane} w ∧
      Tendsto (fun x : ℝ => (x : ℂ) * Complex.exp (-(s * I * γ * x)) * w x) atTop (𝓝 1) := by
  sorry

/-! ### §30.2(ii) Other forms -/

/-- **The Liouville normal form** (DLMF 30.2.2, 30.2.3): if `w` solves 30.2.1 on an open set
`U`, then `g(t) = (sin t)^{1/2} w(cos t)` (so `w(z) = (1-z²)^{-1/4} g(t)` with `z = cos t`)
solves 30.2.2 on every open set `T` of `t` with `cos t ∈ U` and `sin t` in the slit plane
(e.g. a neighbourhood of a subinterval of `(0, π)`). -/
@[dlmf 30.2.E2, dlmf 30.2.E3]
theorem isSpheroidalLiouvilleSolution_of_isSpheroidalSolutionOn {lam γ2 μ : ℂ} {U T : Set ℂ}
    {w : ℂ → ℂ} (hU : IsOpen U) (hT : IsOpen T) (hw : IsSpheroidalSolutionOn lam γ2 μ U w)
    (hTU : ∀ t ∈ T, Complex.cos t ∈ U) (hsin : ∀ t ∈ T, Complex.sin t ∈ slitPlane) :
    IsSpheroidalLiouvilleSolution lam γ2 μ T
      (fun t => Complex.sin t ^ (1 / 2 : ℂ) * w (Complex.cos t)) := by
  sorry

/-- **The form in `ζ = γz`** (DLMF 30.2.4): if `w` solves 30.2.1 on an open set `U` avoiding
`±1` and `γ ≠ 0`, then `ζ ↦ w(ζ/γ)` solves 30.2.4 (with `γ2 = γ²`) on `γU`. -/
@[dlmf 30.2.E4]
theorem isSpheroidalZetaSolution_of_isSpheroidalSolutionOn {lam μ γ : ℂ} {U : Set ℂ}
    {w : ℂ → ℂ} (hγ : γ ≠ 0) (hU : IsOpen U) (hU1 : ∀ z ∈ U, 1 - z ^ 2 ≠ 0)
    (hw : IsSpheroidalSolutionOn lam (γ ^ 2) μ U w) :
    IsSpheroidalZetaSolution lam (γ ^ 2) μ ((fun z => γ * z) '' U) (fun ζ => w (ζ / γ)) := by
  sorry

/-! ### §30.2(iii) Special cases -/

/-- **`γ = 0`: the associated Legendre equation** (DLMF §30.2(iii), 14.2.2): the Ferrers function
`𝖯^m_n(x)` solves 30.2.1 on `(-1, 1)` with `γ = 0`, `λ = n(n+1)`, `μ = m`. -/
@[dlmf 30.2.iii]
theorem isSpheroidalSolutionReal_ferrersP (n m : ℕ) :
    IsSpheroidalSolutionReal ((n : ℝ) * (n + 1)) 0 m
      (fun x => (DLMF.Legendre.ferrersP n m x).re) := by
  sorry

/-- **`μ² = 1/4`: Mathieu's equation** (DLMF §30.2(iii), 28.2.1): for `μ² = 1/4` the coefficient
of 30.2.2 is `λ + 1/4 + γ² sin²t = a - 2q cos 2t` with `a = λ + 1/4 + γ²/2`, `q = γ²/4`, so
30.2.2 is Mathieu's equation `g'' + (a - 2q cos 2t) g = 0` (proved). -/
@[dlmf 30.2.iii]
theorem spheroidalLiouville_coeff_mathieu (lam γ2 μ t : ℂ) (hμ : μ ^ 2 = 1 / 4) :
    lam + 1 / 4 + γ2 * Complex.sin t ^ 2 - (μ ^ 2 - 1 / 4) / Complex.sin t ^ 2 =
      (lam + 1 / 4 + γ2 / 2) - 2 * (γ2 / 4) * Complex.cos (2 * t) := by
  rw [hμ, sub_self, zero_div, sub_zero, Complex.cos_two_mul]
  linear_combination γ2 * Complex.sin_sq_add_cos_sq t

/-- **`μ² = 1/4`: Mathieu's equation** (DLMF §30.2(iii)): a solution of the Liouville form 30.2.2
with `μ² = 1/4` on `T` satisfies `g'' = (2q cos 2t - a) g` with `a = λ + 1/4 + γ²/2`, `q = γ²/4`
(proved). -/
@[dlmf 30.2.iii]
theorem IsSpheroidalLiouvilleSolution.mathieu {lam γ2 μ : ℂ} {T : Set ℂ} {g : ℂ → ℂ}
    (hg : IsSpheroidalLiouvilleSolution lam γ2 μ T g) (hμ : μ ^ 2 = 1 / 4) :
    ∀ t ∈ T, HasDerivAt (deriv g)
      ((2 * (γ2 / 4) * Complex.cos (2 * t) - (lam + 1 / 4 + γ2 / 2)) * g t) t := by
  intro t ht
  convert hg.hasDerivAt t ht using 1
  rw [spheroidalLiouville_coeff_mathieu lam γ2 μ t hμ]
  ring

/-- **`γ = 0` in 30.2.4: the spherical Bessel equation** (DLMF §30.2(iii), 10.47.1): with `γ = 0`
and `μ` arbitrary, 30.2.4 reads `ζ² w'' + 2ζ w' + (ζ² - λ) w = 0`, which for `λ = n(n+1)` is
satisfied by the spherical Bessel function `j_n` (`DLMF.sphericalJ`). -/
@[dlmf 30.2.iii]
theorem isSpheroidalZetaSolution_sphericalJ (n : ℕ) (μ : ℂ) :
    IsSpheroidalZetaSolution ((n : ℂ) * (n + 1)) 0 μ univ (DLMF.sphericalJ n) := by
  sorry

/-! ### §30.3(i) The entire factor -/

/-- **Bounded solutions and the factor equation** (DLMF §30.3(i)): on `(-1, 1)`, for real `λ`,
`γ²`, the function `(1-x²)^{m/2} g(x)` with `g` entire and real on `ℝ` solves 30.2.1 with `μ = m`
iff `g` solves `IsSpheroidalFactor` (the equation holds on `ℂ` by analytic continuation). -/
@[dlmf 30.3.i]
theorem isSpheroidalSolutionReal_iff_isSpheroidalFactor {m : ℕ} {γ2 lam : ℝ} {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hreal : ∀ x : ℝ, (g x).im = 0) :
    IsSpheroidalSolutionReal lam γ2 m (fun x => (1 - x ^ 2) ^ ((m : ℝ) / 2) * (g x).re) ↔
      IsSpheroidalFactor m γ2 lam g := by
  sorry

/-- **Bounded solutions** (DLMF §30.3(i)): for real `λ`, 30.2.1 with `μ = m` has a nonzero
solution bounded on `(-1, 1)` iff `λ` lies in the spectrum, i.e. iff it has a nonzero solution
of the form `(1-x²)^{m/2} g(x)` with `g` entire. -/
@[dlmf 30.3.i]
theorem exists_bounded_iff_mem_spheroidalSpectrum (m : ℕ) (γ2 lam : ℝ) :
    (∃ f : ℝ → ℝ, IsSpheroidalSolutionReal lam γ2 m f ∧ (∃ x ∈ Ioo (-1 : ℝ) 1, f x ≠ 0) ∧
      ∃ C, ∀ x ∈ Ioo (-1 : ℝ) 1, |f x| ≤ C) ↔ lam ∈ spheroidalSpectrum m γ2 := by
  sorry

/-! ### §30.12 Generalized and Coulomb spheroidal functions -/

/-- **Reduction of 30.12.1** (DLMF §30.12): for `α = 0` the generalized equation 30.12.1 is 30.2.1
(proved). -/
@[dlmf 30.12.E1]
theorem isGenSpheroidalSolutionOn_zero_iff {lam γ2 μ : ℂ} {U : Set ℂ} {w : ℂ → ℂ} :
    IsGenSpheroidalSolutionOn lam 0 γ2 μ U w ↔ IsSpheroidalSolutionOn lam γ2 μ U w := by
  constructor
  · intro h
    exact ⟨h.differentiableAt, fun z hz => by simpa using h.hasDerivAt z hz⟩
  · intro h
    exact ⟨h.differentiableAt, fun z hz => by simpa using h.hasDerivAt z hz⟩

/-- **Reduction of 30.12.2** (DLMF §30.12): for `α = 0` the equation 30.12.2 is 30.2.1 (proved). -/
@[dlmf 30.12.E2]
theorem isSpheroidalSolutionOn₂_zero_iff {lam γ2 μ : ℂ} {U : Set ℂ} {w : ℂ → ℂ} :
    IsSpheroidalSolutionOn₂ lam 0 γ2 μ U w ↔ IsSpheroidalSolutionOn lam γ2 μ U w := by
  constructor
  · intro h
    exact ⟨h.differentiableAt, fun z hz => by simpa using h.hasDerivAt z hz⟩
  · intro h
    exact ⟨h.differentiableAt, fun z hz => by simpa using h.hasDerivAt z hz⟩

end DLMF.Spheroidal
