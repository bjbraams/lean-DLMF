/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Heun functions, Heun polynomials and orthogonality (DLMF §§31.4–31.6, 31.9)

* §31.4: for discrete values `q_m` of the accessory parameter `Hl(a, q_m; …; z)` is analytic at
  `z = 1`, hence in `|z| < |a|` (`IsHeunEigenvalue01`, `heunFunction01`); the eigenvalues form an
  infinite discrete set and satisfy the continued-fraction equation 31.4.2.
* §31.5: for `α = -n` and `q` an eigenvalue of the tridiagonal matrix 31.5.1 the series of `Hl`
  terminates: the Heun polynomial `heunPoly` (31.5.2) of degree `n`.
* §31.6: path-multiplicative solutions (definition `IsPathMultiplicative` in Basic).
* §31.9: the single orthogonality of `(0,1)Hf_m` over the Pochhammer double loop
  `(1+, 0+, 1-, 0-)` with the normalization 31.9.3–31.9.4, and the double orthogonality 31.9.5 of
  Heun polynomials.

The index `m` of `q_m`, `(s₁,s₂)Hf_m`, `Hp_{n,m}` is not modelled (DLMF fixes no ordering of
the eigenvalues); statements are about eigenvalues `q`. The predicate `IsHeunFunctionOn` covers
finite pairs `s₁, s₂ ∈ {0, 1, a}` only. Contour integrals use `continuedPathIntegral` along the
explicit loop `pochhammerLoop` (four circles through the base point), with branches continued
along the path and principal values at the start (`localBranchCpow`).

Numerical checks (mpmath): the continued fraction 31.4.2 at an eigenvalue `q₀ ≈ 0.25992` for
`a = 3, α = 0.4, β = 1.2, γ = 0.7, δ = 0.6`; the Pochhammer integral 31.9.2 for the two
eigenvalues `q ≈ -2.9348, 0.25992` (off-diagonal `< 10⁻¹⁹`, diagonal equal to `θ_m` of 31.9.3 to
ten digits); Heun polynomials for `n ≤ 3` (terminating series, ODE residuals `< 10⁻²⁷`).
-/

@[expose] public section

open Complex Filter Set Polynomial
open scoped Topology Real

noncomputable section

namespace DLMF.Heun

variable {a q α β γ δ ε : ℂ}

/-! ### Heun functions (§31.4) -/

/-- DLMF §31.4: if `q = q_m` is an eigenvalue for the pair `(0, 1)` and `|a| > 1`, then
`Hl(a, q_m; α, β, γ, δ; ·)` continues analytically to the whole disk `|z| < |a|`, as a solution
of Heun's equation there (away from `0` and `1`). -/
@[dlmf 31.4, dlmf 31.4.E1]
theorem IsHeunEigenvalue01.analyticOn_ball (ha : 1 < ‖a‖) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (h : IsHeunEigenvalue01 a q α β γ δ) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (Metric.ball 0 ‖a‖) ∧ f =ᶠ[𝓝 0] heunLocal a q α β γ δ ∧
      IsHeunSolOn a q α β γ δ (heunEps α β γ δ) f (Metric.ball 0 ‖a‖ \ {0, 1}) := by
  sorry

/-- DLMF 31.4.1: on the unit disk the Heun function `(0,1)Hf_m` is `Hl(a, q_m; …)` itself. -/
@[dlmf 31.4.E1]
theorem heunFunction01_eq_heunLocal (ha : 1 < ‖a‖) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (h : IsHeunEigenvalue01 a q α β γ δ) {z : ℂ} (hz : ‖z‖ < 1) :
    heunFunction01 a q α β γ δ z = heunLocal a q α β γ δ z := by
  sorry

/-- DLMF §31.4: the eigenvalues `q_m`, `m = 0, 1, 2, …`, form an infinite discrete set: there are
infinitely many, and only finitely many in each disk. Stated for `|a| > 1`, `γ ∉ {0, -1, …}` and
`δ ∉ ℤ` (so that analyticity at `1` is a single condition on `q`, the vanishing of the entire
connection coefficient of the exponent `1 - δ` solution at `1`). -/
@[dlmf 31.4]
theorem heunEigenvalue01_infinite_discrete (ha : 1 < ‖a‖) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (hδ : ∀ n : ℤ, δ ≠ n) :
    {q | IsHeunEigenvalue01 a q α β γ δ}.Infinite ∧
      ∀ R : ℝ, {q | IsHeunEigenvalue01 a q α β γ δ ∧ ‖q‖ ≤ R}.Finite := by
  sorry

/-- DLMF 31.4.2: an eigenvalue `q_m` satisfies the continued-fraction equation
`q = aγP₁/(Q₁ + q - R₁P₂/(Q₂ + q - R₂P₃/(Q₃ + q - ⋯)))`: the approximants converge to `q`.
Hypotheses: `|a| > 1`, `α, β, γ ∉ {0, -1, -2, …}` (all partial numerators `R_{j-1}P_j` nonzero)
and no Maclaurin coefficient `c_j` of `Hl` vanishes (so that the ratios `c_j/c_{j-1}`, the tails
of the fraction by Pincherle's theorem, are defined). -/
@[dlmf 31.4.E2]
theorem tendsto_heunCFApprox (ha : 1 < ‖a‖) (hα : ∀ n : ℕ, α ≠ -(n : ℂ))
    (hβ : ∀ n : ℕ, β ≠ -(n : ℂ)) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (hc : ∀ j, heunLocalCoeff a q α β γ δ j ≠ 0) (h : IsHeunEigenvalue01 a q α β γ δ) :
    Tendsto (heunCFApprox a q α β γ δ) atTop (𝓝 q) := by
  sorry

/-! ### Heun polynomials (§31.5) -/

/-- DLMF 31.5.1–31.5.2: if `α = -n` and `q = q_{n,m}` is an eigenvalue of the matrix 31.5.1,
then (for `a ≠ 0`, `γ ∉ {0, -1, …, 1 - n}`) the coefficients `c_j` of `Hl` vanish for `j > n`, so
`Hl(a, q; -n, β, γ, δ; z)` is the polynomial `Hp_{n,m}(z) = heunPoly a q β γ δ n` for every
`z`. -/
@[dlmf 31.5.E2]
theorem heunLocal_eq_heunPoly (ha : a ≠ 0) {n : ℕ} (hγ : ∀ k : ℕ, k < n → γ ≠ -(k : ℂ))
    (hq : (heunPolyMatrix a β γ δ n).charpoly.IsRoot q) (z : ℂ) :
    (∀ j, n < j → heunLocalCoeff a q (-(n : ℂ)) β γ δ j = 0) ∧
      heunLocal a q (-(n : ℂ)) β γ δ z = (heunPoly a q β γ δ n).eval z := by
  sorry

/-- DLMF §31.5: the Heun polynomial has degree exactly `n` (for `β ∉ {0, -1, …, 1 - n}`) and is a
solution of Heun's equation analytic at all three finite singularities `0, 1, a`. -/
@[dlmf 31.5, dlmf 31.5.E2]
theorem heunPoly_isHeunSolOn (ha : a ≠ 0) {n : ℕ} (hγ : ∀ k : ℕ, k < n → γ ≠ -(k : ℂ))
    (hβ : ∀ k : ℕ, k < n → β ≠ -(k : ℂ))
    (hq : (heunPolyMatrix a β γ δ n).charpoly.IsRoot q) :
    (heunPoly a q β γ δ n).natDegree = n ∧
      IsHeunSolOn a q (-(n : ℂ)) β γ δ (heunEps (-(n : ℂ)) β γ δ)
        (fun z => (heunPoly a q β γ δ n).eval z) {z | z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a} := by
  sorry

/-- DLMF §31.5: there are `n + 1` eigenvalues `q_{n,m}`, `m = 0, …, n`, counted with
multiplicity (the characteristic polynomial of the matrix 31.5.1 has degree `n + 1`). -/
@[dlmf 31.5]
theorem heunPolyMatrix_charpoly_natDegree (a β γ δ : ℂ) (n : ℕ) :
    (heunPolyMatrix a β γ δ n).charpoly.natDegree = n + 1 := by
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-! ### Orthogonality (§31.9) -/

/-- DLMF 31.9.2 (off-diagonal): for two distinct eigenvalues `q_m ≠ q_k` for the pair `(0, 1)`,
`∫_ζ^{(1+,0+,1-,0-)} t^{γ-1}(1-t)^{δ-1}(t-a)^{ε-1} w_m(t) w_k(t) dt = 0`, where
`w = (0,1)Hf(a, q; α, β, γ, δ; ·)`, `ζ ∈ (0, 1)`, the branches are continuous on the path and
principal at the beginning, and `a` lies outside the two circles of the loop
(`|a| > ζ`, `|a - 1| > 1 - ζ`). -/
@[dlmf 31.9.E1, dlmf 31.9.E2]
theorem heun_orthogonality_ne (ha : 1 < ‖a‖) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (hδ : ∀ n : ℕ, δ ≠ -(n : ℂ)) {ζ : ℝ} (hζ : ζ ∈ Ioo (0 : ℝ) 1) (ha1 : 1 - ζ < ‖a - 1‖)
    {q₁ q₂ : ℂ} (h₁ : IsHeunEigenvalue01 a q₁ α β γ δ) (h₂ : IsHeunEigenvalue01 a q₂ α β γ δ)
    (hne : q₁ ≠ q₂) :
    continuedPathIntegral (pochhammerLoop 0 1 ζ)
      (fun t => localBranchCpow ζ (γ - 1) t * localBranchCpow (1 - ζ) (δ - 1) (1 - t) *
        localBranchCpow (ζ - a) (heunEps α β γ δ - 1) (t - a) *
        heunLocal a q₁ α β γ δ t * heunLocal a q₂ α β γ δ t) = 0 := by
  sorry

/-- DLMF 31.9.2–31.9.4 (diagonal): for an eigenvalue `q_m` the Pochhammer integral of
`t^{γ-1}(1-t)^{δ-1}(t-a)^{ε-1} w_m(t)²` equals
`θ_m = (1 - e^{2πiγ})(1 - e^{2πiδ}) ζ^γ (1-ζ)^δ (ζ-a)^ε (f₀/f₁)(q_m, ζ)
∂_q 𝒲{f₀(q, ζ), f₁(q, ζ)}|_{q = q_m}`, with `f₀(q, z) = Hl(a, q; α, β, γ, δ; z)`,
`f₁(q, z) = Hl(1 - a, αβ - q; α, β, δ, γ; 1 - z)` and the Wronskian
`𝒲{f₀, f₁} = f₀ ∂_z f₁ - ∂_z f₀ f₁` (principal powers). -/
@[dlmf 31.9.E2, dlmf 31.9.E3, dlmf 31.9.E4]
theorem heun_orthogonality_self (ha : 1 < ‖a‖) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (hδ : ∀ n : ℕ, δ ≠ -(n : ℂ)) {ζ : ℝ} (hζ : ζ ∈ Ioo (0 : ℝ) 1) (ha1 : 1 - ζ < ‖a - 1‖)
    {qm : ℂ} (hm : IsHeunEigenvalue01 a qm α β γ δ) :
    continuedPathIntegral (pochhammerLoop 0 1 ζ)
      (fun t => localBranchCpow ζ (γ - 1) t * localBranchCpow (1 - ζ) (δ - 1) (1 - t) *
        localBranchCpow (ζ - a) (heunEps α β γ δ - 1) (t - a) *
        heunLocal a qm α β γ δ t * heunLocal a qm α β γ δ t) =
      (1 - cexp (2 * π * I * γ)) * (1 - cexp (2 * π * I * δ)) * (ζ : ℂ) ^ γ *
        (1 - (ζ : ℂ)) ^ δ * ((ζ : ℂ) - a) ^ heunEps α β γ δ *
        (heunLocal a qm α β γ δ ζ / heunLocal (1 - a) (α * β - qm) α β δ γ (1 - ζ)) *
        deriv (fun q => heunLocal a q α β γ δ ζ *
            deriv (fun z => heunLocal (1 - a) (α * β - q) α β δ γ (1 - z)) ζ -
          deriv (fun z => heunLocal a q α β γ δ z) ζ *
            heunLocal (1 - a) (α * β - q) α β δ γ (1 - ζ)) qm := by
  sorry

/-- DLMF 31.9.5–31.9.6, double orthogonality of Heun polynomials. Fix `a, γ, δ, ε`; for
`i = 1, 2` let `w_i = Hp_{n_i}(a, q_i; -n_i, β_i, γ, δ; ·)` with `β_i = γ + δ + ε - 1 + n_i`
(so that `ε` is the same) and `q_i` an eigenvalue of the matrix 31.5.1, the two being different.
For Pochhammer loops `𝓛₁`, `𝓛₂` around two distinct pairs `{p₁, p₂}`, `{p₃, p₄}` of
singularities from `{0, 1, a}` (base points `ζ₁, ζ₂` on the joining segments, the third
singularity outside both circles of each loop),
`∫_{𝓛₁}∫_{𝓛₂} ρ(s,t) w₁(s)w₁(t)w₂(s)w₂(t) ds dt = 0` with
`ρ(s,t) = (s-t)(st)^{γ-1}((s-1)(t-1))^{δ-1}((s-a)(t-a))^{ε-1}`. Since `ρ(s,t) = (s-t)h(s)h(t)`,
the double integral is stated in its factorized form
`(∫_{𝓛₁} s u(s) ds)(∫_{𝓛₂} u(t) dt) - (∫_{𝓛₁} u(s) ds)(∫_{𝓛₂} t u(t) dt)`,
`u = h w₁ w₂`, `h(x) = x^{γ-1}(x-1)^{δ-1}(x-a)^{ε-1}` (any initial branch). -/
@[dlmf 31.9.E5, dlmf 31.9.E6]
theorem heunPoly_double_orthogonality (ha0 : a ≠ 0) (ha1 : a ≠ 1) {n₁ n₂ : ℕ} {q₁ q₂ : ℂ}
    (hγ : ∀ k : ℕ, γ ≠ -(k : ℂ)) (hδ : ∀ k : ℕ, δ ≠ -(k : ℂ))
    (hq₁ : (heunPolyMatrix a (γ + δ + ε - 1 + n₁) γ δ n₁).charpoly.IsRoot q₁)
    (hq₂ : (heunPolyMatrix a (γ + δ + ε - 1 + n₂) γ δ n₂).charpoly.IsRoot q₂)
    (hne : n₁ ≠ n₂ ∨ q₁ ≠ q₂) {p₁ p₂ p₃ p₄ ζ₁ ζ₂ : ℂ}
    (hp : ∀ p ∈ ({p₁, p₂, p₃, p₄} : Set ℂ), p = 0 ∨ p = 1 ∨ p = a)
    (hp₁₂ : p₁ ≠ p₂) (hp₃₄ : p₃ ≠ p₄) (hpairs : ({p₁, p₂} : Set ℂ) ≠ {p₃, p₄})
    (hζ₁ : ∃ s ∈ Ioo (0 : ℝ) 1, ζ₁ = p₁ + s * (p₂ - p₁))
    (hζ₂ : ∃ s ∈ Ioo (0 : ℝ) 1, ζ₂ = p₃ + s * (p₄ - p₃))
    (hout₁ : ∀ r ∈ ({0, 1, a} : Set ℂ), r ≠ p₁ → r ≠ p₂ →
      ‖ζ₁ - p₁‖ < ‖r - p₁‖ ∧ ‖ζ₁ - p₂‖ < ‖r - p₂‖)
    (hout₂ : ∀ r ∈ ({0, 1, a} : Set ℂ), r ≠ p₃ → r ≠ p₄ →
      ‖ζ₂ - p₃‖ < ‖r - p₃‖ ∧ ‖ζ₂ - p₄‖ < ‖r - p₄‖) :
    let u : ℂ → ℂ → ℂ := fun ζ x => localBranchCpow ζ (γ - 1) x *
      localBranchCpow (ζ - 1) (δ - 1) (x - 1) * localBranchCpow (ζ - a) (ε - 1) (x - a) *
      (heunPoly a q₁ (γ + δ + ε - 1 + n₁) γ δ n₁).eval x *
      (heunPoly a q₂ (γ + δ + ε - 1 + n₂) γ δ n₂).eval x
    continuedPathIntegral (pochhammerLoop p₁ p₂ ζ₁) (fun s => s * u ζ₁ s) *
        continuedPathIntegral (pochhammerLoop p₃ p₄ ζ₂) (u ζ₂) -
      continuedPathIntegral (pochhammerLoop p₁ p₂ ζ₁) (u ζ₁) *
        continuedPathIntegral (pochhammerLoop p₃ p₄ ζ₂) (fun t => t * u ζ₂ t) = 0 := by
  sorry

end DLMF.Heun
