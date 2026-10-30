/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Basic
public import DLMF.Bessel.Basic
public import DLMF.Painleve.Basic
public import Mathlib.RingTheory.Binomial

/-!
# Differential and difference equations: definitions (DLMF §§2.7–2.9)

Definitions for DLMF §§2.7–2.9 (namespace `DLMF.AsymptoticApproximations`).

* `IsLinearODE2SolOn f g w U`: `w'' + f w' + g w = 0` on `U ⊆ ℂ` (2.7.1), via the project's
  `DLMF.Painleve.IsODE2SolutionOn`.
* `IsLogPlaneSolOn f g W U`: the same equation on the logarithmic plane, `W(ζ) = w(e^ζ)`, used
  for solutions continued over sectors of opening larger than `2π` (2.7.14–2.7.17).
* `indicialPoly`, `frobeniusCoeff`: the indicial equation 2.7.3 and the Frobenius recursion
  2.7.5 at a regular singularity.
* `HasSingularityRank`: the rank of a singularity (§2.7(ii)).
* `rankOneExponent`, `rankOneCoeff`: the exponent 2.7.10 and the recursion 2.7.11 of the
  formal solutions 2.7.8 at an irregular singularity of rank 1 at infinity.
* `airyEnvCrit`, `envAi`, `envBi` (2.8.19–2.8.21) and `besselEnvCrit`, `envJ`, `envY`
  (2.8.32–2.8.34): the envelope functions of §2.8.
* `differenceExponent`, `differenceCoeff`: the exponent 2.9.6 and the recursion 2.9.7 of the
  formal solutions 2.9.4 of three-term recurrences.

The singular-point classification itself is DLMFMathlib's `Complex.LinearODEOrdinaryAt`,
`Complex.LinearODERegularSingularAt` and `Complex.LinearODEIrregularAt` applied to the
coefficient vector `![g, f]` (coefficient of `w` first).
-/

@[expose] public noncomputable section

open Set Complex Filter
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-! ### §2.7 -/

/-- DLMF 2.7.1: `w'' + f(z) w' + g(z) w = 0` on `U ⊆ ℂ`, with `w` and `w'` complex
differentiable at every point of `U`. -/
@[dlmf 2.7.E1]
def IsLinearODE2SolOn (f g : ℂ → ℂ) (w : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DLMF.Painleve.IsODE2SolutionOn (fun z w w' => -(f z * w' + g z * w)) w U

/-- The equation 2.7.1 on the logarithmic plane: `W(ζ) = w(e^ζ)` satisfies
`W'' - W' + e^ζ f(e^ζ) W' + e^{2ζ} g(e^ζ) W = 0` (since `z d/dz = d/dζ`). Solutions of 2.7.1
continued along arcs around the origin are functions of `ζ`, and `ph z = ℑζ`. -/
@[dlmf 2.7.E1]
def IsLogPlaneSolOn (f g : ℂ → ℂ) (W : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DLMF.Painleve.IsODE2SolutionOn
    (fun ζ W W' => W' - exp ζ * f (exp ζ) * W' - exp (2 * ζ) * g (exp ζ) * W) W U

/-- The indicial polynomial `Q(α) = α(α-1) + f₀α + g₀` (DLMF 2.7.3). -/
@[dlmf 2.7.E3]
def indicialPoly (f₀ g₀ α : ℂ) : ℂ := α * (α - 1) + f₀ * α + g₀

/-- The Frobenius coefficients `a_s` at a regular singularity (DLMF 2.7.5): `a_0 = 1` and
`Q(α+s) a_s = -∑_{r<s} ((α+r) f_{s-r} + g_{s-r}) a_r`, for the Laurent coefficients
`f(z) = ∑ f_s (z-z₀)^{s-1}`, `g(z) = ∑ g_s (z-z₀)^{s-2}` (2.7.2). When `Q(α+s) = 0` the value
is Lean's `x / 0 = 0`; the theorems exclude this case. -/
@[dlmf 2.7.E5]
def frobeniusCoeff (fs gs : ℕ → ℂ) (α : ℂ) : ℕ → ℂ
  | 0 => 1
  | s + 1 => -(∑ r : Fin (s + 1), ((α + r) * fs (s + 1 - r) + gs (s + 1 - r)) *
      frobeniusCoeff fs gs α r) / indicialPoly (fs 0) (gs 0) (α + (s + 1))
  decreasing_by exact r.isLt

/-- The singularity of 2.7.1 at `z₀` has rank `r` (DLMF §2.7(ii)): the coefficients have at
most poles at `z₀`, and `ℓ = r + 1` is the least natural number such that `(z-z₀)^ℓ f(z)` and
`(z-z₀)^{2ℓ} g(z)` are analytic at `z₀` (after removing a removable singularity). -/
@[dlmf 2.7.ii]
def HasSingularityRank (f g : ℂ → ℂ) (z₀ : ℂ) (r : ℕ) : Prop :=
  IsLeast {ℓ : ℕ | 1 ≤ ℓ ∧ (∃ F : ℂ → ℂ, AnalyticAt ℂ F z₀ ∧
      (fun z => (z - z₀) ^ ℓ * f z) =ᶠ[𝓝[≠] z₀] F) ∧
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G z₀ ∧ (fun z => (z - z₀) ^ (2 * ℓ) * g z) =ᶠ[𝓝[≠] z₀] G}
    (r + 1)

/-- The exponent `μ_j = -(f₁λ_j + g₁)/(f₀ + 2λ_j)` of the formal solution 2.7.8 (DLMF 2.7.10),
where `λ_j` is a root of the characteristic equation `λ² + f₀λ + g₀ = 0` (2.7.9). -/
@[dlmf 2.7.E10]
def rankOneExponent (fs gs : ℕ → ℂ) (lam : ℂ) : ℂ :=
  -(fs 1 * lam + gs 1) / (fs 0 + 2 * lam)

/-- The coefficients `a_{s,j}` of the formal solution `e^{λ z} z^{μ} ∑ a_s z^{-s}` (2.7.8) at a
rank-one irregular singularity at infinity (DLMF 2.7.11): `a_0 = 1` and
`(f₀ + 2λ) s a_s = (s-μ)(s-1-μ) a_{s-1} + ∑_{r=1}^{s} (λ f_{r+1} + g_{r+1} - (s-r-μ) f_r) a_{s-r}`,
with `μ = rankOneExponent fs gs λ` and `f(z) = ∑ f_s z^{-s}`, `g(z) = ∑ g_s z^{-s}` (2.7.7). -/
@[dlmf 2.7.E11, dlmf 2.7.E8]
def rankOneCoeff (fs gs : ℕ → ℂ) (lam : ℂ) : ℕ → ℂ
  | 0 => 1
  | s + 1 =>
    (((s + 1 : ℂ) - rankOneExponent fs gs lam) * ((s : ℂ) - rankOneExponent fs gs lam) *
        rankOneCoeff fs gs lam s +
      ∑ r : Fin (s + 1), (lam * fs (r + 2) + gs (r + 2) -
          ((s : ℂ) - r - rankOneExponent fs gs lam) * fs (r + 1)) *
        rankOneCoeff fs gs lam (s - r)) / ((fs 0 + 2 * lam) * (s + 1))
  decreasing_by all_goals omega

/-! ### §2.8 Envelope functions -/

/-- The constant `c = -0.36604…` of DLMF 2.8.19: the real root of `Ai(x) = Bi(x)` of smallest
absolute value. All real roots are negative, so `c` is the largest root. -/
@[dlmf 2.8.E19]
def airyEnvCrit : ℝ :=
  sSup {x : ℝ | x ≤ 0 ∧ DLMF.Airy.airyAi x = DLMF.Airy.airyBi x}

/-- The envelope `envAi` of `Ai` (DLMF 2.8.20–2.8.21): `(Ai² + Bi²)^{1/2}` for `x ≤ c` and
`√2 Ai(x)` for `x ≥ c`. -/
@[dlmf 2.8.E20, dlmf 2.8.E21]
def envAi (x : ℝ) : ℝ :=
  if x ≤ airyEnvCrit then
    Real.sqrt ((DLMF.Airy.airyAi x).re ^ 2 + (DLMF.Airy.airyBi x).re ^ 2)
  else Real.sqrt 2 * (DLMF.Airy.airyAi x).re

/-- The envelope `envBi` of `Bi` (DLMF 2.8.20–2.8.21): `(Ai² + Bi²)^{1/2}` for `x ≤ c` and
`√2 Bi(x)` for `x ≥ c`. -/
@[dlmf 2.8.E20, dlmf 2.8.E21]
def envBi (x : ℝ) : ℝ :=
  if x ≤ airyEnvCrit then
    Real.sqrt ((DLMF.Airy.airyAi x).re ^ 2 + (DLMF.Airy.airyBi x).re ^ 2)
  else Real.sqrt 2 * (DLMF.Airy.airyBi x).re

/-- The constant `X_ν` of DLMF 2.8.32: the smallest positive root of `J_ν(x) + Y_ν(x) = 0`. -/
@[dlmf 2.8.E32]
def besselEnvCrit (ν : ℝ) : ℝ :=
  sInf {x : ℝ | 0 < x ∧ Complex.besselJ ν x + DLMF.Bessel.besselY ν x = 0}

/-- The envelope `env J_ν` (DLMF 2.8.33–2.8.34): `√2 J_ν(x)` for `0 < x ≤ X_ν` and
`(J_ν² + Y_ν²)^{1/2}` for `x ≥ X_ν`. -/
@[dlmf 2.8.E33, dlmf 2.8.E34]
def envJ (ν x : ℝ) : ℝ :=
  if x ≤ besselEnvCrit ν then Real.sqrt 2 * (Complex.besselJ ν x).re
  else Real.sqrt ((Complex.besselJ ν x).re ^ 2 + (DLMF.Bessel.besselY ν x).re ^ 2)

/-- The envelope `env Y_ν` (DLMF 2.8.33–2.8.34): `√2 |Y_ν(x)|` for `0 < x ≤ X_ν` and
`(J_ν² + Y_ν²)^{1/2}` for `x ≥ X_ν`. -/
@[dlmf 2.8.E33, dlmf 2.8.E34]
def envY (ν x : ℝ) : ℝ :=
  if x ≤ besselEnvCrit ν then Real.sqrt 2 * |(DLMF.Bessel.besselY ν x).re|
  else Real.sqrt ((Complex.besselJ ν x).re ^ 2 + (DLMF.Bessel.besselY ν x).re ^ 2)

/-! ### §2.9 Difference equations -/

/-- The exponent `α_j = (f₁ρ_j + g₁)/(f₀ρ_j + 2g₀)` of the formal solution 2.9.4 (DLMF 2.9.6),
where `ρ_j` is a root of `ρ² + f₀ρ + g₀ = 0` (2.9.5). -/
@[dlmf 2.9.E6]
def differenceExponent (fs gs : ℕ → ℂ) (ρ : ℂ) : ℂ :=
  (fs 1 * ρ + gs 1) / (fs 0 * ρ + 2 * gs 0)

/-- The coefficients `a_{s,j}` of the formal solution `ρⁿ n^{α} ∑ a_s n^{-s}` (2.9.4) of the
recurrence 2.9.1 (DLMF 2.9.7): `a_0 = 1` and
`ρ(f₀ + 2ρ) s a_s = ∑_{r=1}^{s} (ρ² 2^{r+1} (α+r-s choose r+1)
  + ρ ∑_{q=0}^{r+1} (α+r-s choose r+1-q) f_q + g_{r+1}) a_{s-r}`,
with `α = differenceExponent fs gs ρ` and Mathlib's generalized binomial `Ring.choose`. -/
@[dlmf 2.9.E7, dlmf 2.9.E4]
def differenceCoeff (fs gs : ℕ → ℂ) (ρ : ℂ) : ℕ → ℂ
  | 0 => 1
  | s + 1 =>
    (∑ r : Fin (s + 1),
      (ρ ^ 2 * 2 ^ ((r : ℕ) + 2) *
          Ring.choose (differenceExponent fs gs ρ + (r + 1) - (s + 1)) ((r : ℕ) + 2) +
        ρ * ∑ q ∈ Finset.range ((r : ℕ) + 3),
          Ring.choose (differenceExponent fs gs ρ + (r + 1) - (s + 1)) ((r : ℕ) + 2 - q) * fs q +
        gs ((r : ℕ) + 2)) * differenceCoeff fs gs ρ (s - r)) /
      (ρ * (fs 0 + 2 * ρ) * (s + 1))
  decreasing_by all_goals omega

/-- The relations of DLMF 2.9.7 for coefficients `a_s` with a prescribed exponent `α`:
`a_0 = 1` and, for `s ≥ 1`,
`ρ(f₀ + 2ρ) s a_s = ∑_{r=1}^{s} (ρ² 2^{r+1} (α+r-s choose r+1)
  + ρ ∑_{q=0}^{r+1} (α+r-s choose r+1-q) f_q + g_{r+1}) a_{s-r}`.
In the coincident case of §2.9(ii) (`f₀ = -2ρ`) the left side vanishes and the relations are
implicit (DLMF 2.9.12). -/
@[dlmf 2.9.E7]
def IsDifferenceCoeffRel (fs gs : ℕ → ℂ) (ρ α : ℂ) (a : ℕ → ℂ) : Prop :=
  a 0 = 1 ∧ ∀ s, 1 ≤ s → ρ * (fs 0 + 2 * ρ) * s * a s =
    ∑ r ∈ Finset.Icc 1 s, (ρ ^ 2 * 2 ^ (r + 1) * Ring.choose (α + r - s) (r + 1) +
      ρ * ∑ q ∈ Finset.range (r + 2), Ring.choose (α + r - s) (r + 1 - q) * fs q +
      gs (r + 1)) * a (s - r)

/-- The forward difference `Δw(n) = w(n+1) - w(n)` (DLMF §3.6(i)), used in 2.9.2. -/
def g2b_fwdDiff (w : ℕ → ℂ) (n : ℕ) : ℂ := w (n + 1) - w n

/-- The scale `n ↦ n^{-s}` of the coefficient expansions 2.9.3. -/
def g2b_invPowScale (s n : ℕ) : ℂ := ((n : ℂ) ^ s)⁻¹

/-- The scale `n ↦ ρⁿ n^{α-s}` (principal power, `n > 0`) of the expansions 2.9.4, 2.9.8 and
2.9.12. -/
def g2b_diffScale (ρ α : ℂ) (s n : ℕ) : ℂ := ρ ^ n * (n : ℂ) ^ (α - s)

/-- The scale `n ↦ ρⁿ exp(σκ√n) n^{α-s/2}` of DLMF 2.9.9 (`σ = ±1`). -/
def g2b_sqrtScale (ρ κ α : ℂ) (σ : ℂ) (s n : ℕ) : ℂ :=
  ρ ^ n * Complex.exp (σ * κ * Real.sqrt n) * (n : ℂ) ^ (α - s / 2)

/-- `w` solves the three-term recurrence `w(n+2) + f(n) w(n+1) + g(n) w(n) = 0` (DLMF 2.9.1)
for all `n = 0, 1, 2, …`. -/
def IsRecurrenceSol (f g w : ℕ → ℂ) : Prop := ∀ n, w (n + 2) + f n * w (n + 1) + g n * w n = 0

section

open Asymptotics

/-- The punctured slit disc `{z : z - z₀ ∉ (-∞, 0], |z - z₀| < R}` on which the principal powers
`(z - z₀)^{α}` are holomorphic. -/
def g2b_slitDisc (z₀ : ℂ) (R : ℝ) : Set ℂ :=
  {z : ℂ | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < R}

/-- The filter `|z| → ∞` with `θ₁ ≤ ℑ(ζ + c) ≤ θ₂` on the logarithmic plane (`z = e^ζ`); with
`c = Log(λ₂ - λ₁)` the condition is `θ₁ ≤ ph((λ₂ - λ₁) z) ≤ θ₂`. -/
def logSectorFilter (θ₁ θ₂ : ℝ) (c : ℂ) : Filter ℂ :=
  comap (fun ζ : ℂ => Real.exp ζ.re) atTop ⊓ 𝓟 {ζ : ℂ | θ₁ ≤ (ζ + c).im ∧ (ζ + c).im ≤ θ₂}

/-- The asymptotic scale `e^{λ z} ((λ₂-λ₁) z)^{μ} z^{-s}` of DLMF 2.7.14 on the logarithmic
plane: `exp(λ e^ζ + μ (ζ + c) - s ζ)` with `c = Log(λ₂ - λ₁)`. -/
def rankOneScale (lam μ c : ℂ) (s : ℕ) (ζ : ℂ) : ℂ :=
  exp (lam * exp ζ + μ * (ζ + c) - s * ζ)

/-- The rank-one data: `f(z) = ∑ f_s z^{-s}`, `g(z) = ∑ g_s z^{-s}` converge for `|z| > a`
(DLMF 2.7.7), and `λ₁ ≠ λ₂` are the roots of `λ² + f₀λ + g₀ = 0` (2.7.9). -/
structure IsRankOneAtInfinity (f g : ℂ → ℂ) (fs gs : ℕ → ℂ) (a : ℝ) (l₁ l₂ : ℂ) : Prop where
  /-- The radius of the exterior convergence region is nonnegative. -/
  a_nonneg : 0 ≤ a
  /-- The reciprocal-power series with coefficients fs converges to f outside the prescribed
  circle. -/
  hasSum_f : ∀ z : ℂ, a < ‖z‖ → HasSum (fun s => fs s * z⁻¹ ^ s) (f z)
  /-- The reciprocal-power series with coefficients gs converges to g outside the prescribed
  circle. -/
  hasSum_g : ∀ z : ℂ, a < ‖z‖ → HasSum (fun s => gs s * z⁻¹ ^ s) (g z)
  /-- The characteristic roots have sum `-f₀`. -/
  sum_roots : l₁ + l₂ = -fs 0
  /-- The characteristic roots have product `g₀`. -/
  prod_roots : l₁ * l₂ = gs 0
  /-- The characteristic roots are distinct. -/
  roots_ne : l₁ ≠ l₂

/-- The region `|z| > a` on the logarithmic plane. -/
def g2b_logExterior (a : ℝ) : Set ℂ := {ζ : ℂ | a < Real.exp ζ.re}

end

section

open MeasureTheory

/-- The Liouville–Green approximant `f^{-1/4}(x) exp(σ ξ(x))`, `σ = ±1`. -/
def lgApproximant (f ξ : ℝ → ℝ) (σ : ℝ) (x : ℝ) : ℝ :=
  f x ^ (-(1 / 4) : ℝ) * Real.exp (σ * ξ x)

/-- `w` is a twice-differentiable solution of `w'' = (f + g) w` (DLMF 2.7.20) on `S`. -/
def IsLGSolOn (f g w : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∃ w' : ℝ → ℝ, ∀ x ∈ S, HasDerivAt w (w' x) x ∧ HasDerivAt w' ((f x + g x) * w x) x

/-- The regularity hypotheses of the Liouville–Green theorem on `S`: `f > 0` with derivatives
`f'`, `f''`, `f''` and `g` continuous, and `ξ' = f^{1/2}` (`ξ = ∫ f^{1/2} dx`). -/
structure IsLGData (f f' f'' g ξ : ℝ → ℝ) (S : Set ℝ) : Prop where
  /-- The leading Liouville-Green coefficient f is strictly positive on S. -/
  pos : ∀ x ∈ S, 0 < f x
  /-- The displayed function f-prime is the derivative of f on S. -/
  hasDerivAt_f : ∀ x ∈ S, HasDerivAt f (f' x) x
  /-- The displayed function f-double-prime is the derivative of f-prime on S. -/
  hasDerivAt_f' : ∀ x ∈ S, HasDerivAt f' (f'' x) x
  /-- The second derivative of the leading coefficient is continuous on S. -/
  continuousOn_f'' : ContinuousOn f'' S
  /-- The lower-order coefficient g is continuous on S. -/
  continuousOn_g : ContinuousOn g S
  /-- The phase derivative is `ξ′ = √f` on S. -/
  hasDerivAt_ξ : ∀ x ∈ S, HasDerivAt ξ (√(f x)) x

end

section

open MeasureTheory

/-- The coefficient relations of DLMF 2.8.17–2.8.18 (Case II): `A_0 = 1`,
`B_s(ξ) = (2ξ^{1/2})⁻¹ ∫₀^ξ (ψ A_s - A_s'') v^{-1/2} dv` for `ξ > 0` (and the reflected formula
for `ξ < 0`), and `A_{s+1}' = -½ B_s'' + ½ ψ B_s` (2.8.18 differentiated; the constants of
integration are arbitrary). `Ad s`, `Ad2 s` and `Bd s`, `Bd2 s` are the first two derivatives of
`A s` and `B s`. -/
structure IsAiryCoeffs (ψ : ℝ → ℝ) (α₁ α₂ : ℝ) (A Ad Ad2 B Bd Bd2 : ℕ → ℝ → ℝ) : Prop where
  /-- The leading Airy coefficient A is identically one. -/
  A_zero : ∀ ξ, A 0 ξ = 1
  /-- Ad is the first derivative of each A coefficient on the coefficient interval. -/
  hasDerivAt_A : ∀ s, ∀ ξ ∈ Ioo α₁ α₂, HasDerivAt (A s) (Ad s ξ) ξ
  /-- Ad2 is the second derivative of each A coefficient on the coefficient interval. -/
  hasDerivAt_Ad : ∀ s, ∀ ξ ∈ Ioo α₁ α₂, HasDerivAt (Ad s) (Ad2 s ξ) ξ
  /-- Bd is the first derivative of each B coefficient on the coefficient interval. -/
  hasDerivAt_B : ∀ s, ∀ ξ ∈ Ioo α₁ α₂, HasDerivAt (B s) (Bd s ξ) ξ
  /-- Bd2 is the second derivative of each B coefficient on the coefficient interval. -/
  hasDerivAt_Bd : ∀ s, ∀ ξ ∈ Ioo α₁ α₂, HasDerivAt (Bd s) (Bd2 s ξ) ξ
  /-- On the positive side of the turning point, the weighted integral of `ψ A_s - A_s″` defines
  B_s. -/
  B_pos : ∀ s, ∀ ξ ∈ Ioo α₁ α₂, 0 < ξ →
    B s ξ = (2 * √ξ)⁻¹ * ∫ v in (0 : ℝ)..ξ, (ψ v * A s v - Ad2 s v) / √v
  /-- On the negative side of the turning point, the reflected weighted integral defines B_s. -/
  B_neg : ∀ s, ∀ ξ ∈ Ioo α₁ α₂, ξ < 0 →
    B s ξ = (2 * √(-ξ))⁻¹ * ∫ v in ξ..0, (ψ v * A s v - Ad2 s v) / √(-v)
  /-- The next A coefficient satisfies `A_(s+1)′ = -B_s″/2 + ψ B_s/2`. -/
  A_succ : ∀ s, ∀ ξ ∈ Ioo α₁ α₂, Ad (s + 1) ξ = -(1 / 2) * Bd2 s ξ + 1 / 2 * ψ ξ * B s ξ

/-- The coefficient relations of DLMF 2.8.27–2.8.28 and 2.8.31 (Case III): `A_0 = 1`,
`B_s = -A_s' + |ξ|^{-1/2} ∫ (ψ A_s - (ν + ½) A_s') |v|^{-1/2} dv` (from `0` to `ξ` for
`ξ > 0`, 2.8.27; from `ξ` to `0` for `ξ < 0`, 2.8.31), and
`A_{s+1}' = ν B_s' - (ξ B_s')' + ψ B_s` (2.8.28 differentiated). -/
structure IsBesselCoeffs (ψ : ℝ → ℝ) (ν α₁ α₂ : ℝ) (A Ad B Bd Bd2 : ℕ → ℝ → ℝ) : Prop where
  /-- The leading Bessel coefficient A is identically one. -/
  A_zero : ∀ ξ, A 0 ξ = 1
  /-- Ad is the derivative of each A coefficient on the coefficient interval. -/
  hasDerivAt_A : ∀ s, ∀ ξ ∈ Ioo α₁ α₂, HasDerivAt (A s) (Ad s ξ) ξ
  /-- Bd is the derivative of each B coefficient on the coefficient interval. -/
  hasDerivAt_B : ∀ s, ∀ ξ ∈ Ioo α₁ α₂, HasDerivAt (B s) (Bd s ξ) ξ
  /-- Bd2 is the second derivative of each B coefficient on the coefficient interval. -/
  hasDerivAt_Bd : ∀ s, ∀ ξ ∈ Ioo α₁ α₂, HasDerivAt (Bd s) (Bd2 s ξ) ξ
  /-- The positive-side weighted integral recurrence determines B_s from A_s and its derivative. -/
  B_pos : ∀ s, ∀ ξ ∈ Ioo α₁ α₂, 0 < ξ → B s ξ = -Ad s ξ +
    (√ξ)⁻¹ * ∫ v in (0 : ℝ)..ξ, (ψ v * A s v - (ν + 1 / 2) * Ad s v) / √v
  /-- The reflected negative-side integral recurrence determines B_s from A_s and its derivative. -/
  B_neg : ∀ s, ∀ ξ ∈ Ioo α₁ α₂, ξ < 0 → B s ξ = -Ad s ξ +
    (√(-ξ))⁻¹ * ∫ v in ξ..0, (ψ v * A s v - (ν + 1 / 2) * Ad s v) / √(-v)
  /-- The next A coefficient satisfies `A_(s+1)′ = ν B_s′ - (ξ B_s′)′ + ψ B_s`. -/
  A_succ : ∀ s, ∀ ξ ∈ Ioo α₁ α₂,
    Ad (s + 1) ξ = ν * Bd s ξ - (Bd s ξ + ξ * Bd2 s ξ) + ψ ξ * B s ξ

end

end DLMF.AsymptoticApproximations
