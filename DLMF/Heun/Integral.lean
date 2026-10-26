/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMF.Hypergeometric.Riemann
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# Solutions via quadratures, integral equations and representations (DLMF §31.8, §31.10)

* §31.8: finite-gap (Hermite–Darboux) solutions for half-odd-integer exponent parameters
  (31.8.1): `w_± = √Ψ exp(±(iν/2) ∫ t^{m₁}(t-1)^{m₂}(t-a)^{m₃}/(Ψ √(t(t-1)(t-a))) dt)` (31.8.2),
  with `Ψ` a polynomial solution of the third-order equation for products of solutions, of
  degree `g` (31.8.3) in `λ = -4q`, and the examples 31.8.4–31.8.5. The square root and the
  integral are represented by arbitrary analytic branches `S² = Ψ`, `G' = integrand` on an
  open set, so no branch choice is imposed. The remarks on Hermite's Lamé solutions, the finite-gap
  property, the limit at the gap ends and Kovacic's algorithm are not acquired.
* §31.10(i) (Type I): the integral equation/representation 31.10.1–31.10.6, the kernel
  equation in the variables 31.10.7 (31.10.8, **sign corrected**), its separable solutions
  31.10.9, and the kernels of Examples 1 and 2 (31.10.10, 31.10.11).
* §31.10(ii) (Type II): the double-integral representation 31.10.12–31.10.16, the kernel equation
  in the variables 31.10.17 (**corrected**) and 31.10.18, its solutions 31.10.19 in cylinder
  functions, the spherical form 31.10.20–31.10.21 and its separable solutions 31.10.22–31.10.23
  (**corrected**).

The integral theorems are stated for a single-valued branch `ρ` of the weight on an open set
(any `ρ` with the logarithmic derivative of `t^{γ-1}(t-1)^{δ-1}(t-a)^{ε-1}`) and a `C¹` path in
that set, with the boundary terms 31.10.5 (31.10.15–31.10.16) equal at the two ends; DLMF's
Pochhammer-contour cases need continuation of the branches along the contour and are covered
only in the example statements via `continuedPathIntegral`.

Source corrections (numerical evidence, mpmath, complex parameters; scripts in the agent's
scratch directory):

* **31.10.8**: the coefficient of `∂𝒦/∂φ` is `(2δ - 1) cot φ - (2ε - 1) tan φ`, not
  `(1 - 2δ) cot φ - (1 - 2ε) tan φ`. Evidence: the verified kernel 31.10.10 (it satisfies
  `(𝒟_z - 𝒟_t)𝒦 = 0` to `10⁻³²`) written in `(θ, φ)` via 31.10.7 satisfies the corrected
  equation to `10⁻³¹` and the printed one with residual `1.18` (`|𝒦| ≈ 0.056`); the product
  31.10.9 of the two P-symbol solutions likewise (`4·10⁻²⁹` vs `258`). The P-symbol 31.10.9
  (exponents `{0, 1-ε}` at `cos²φ = 0`) is consistent only with the corrected sign.
* **31.10.17**: `u = (stz/a)^{1/2}`, not `(stz)^{1/2}/a`. Evidence: with the printed `u`, the
  kernels `u^{2-2γ}`, `u²/(2γ) - v²/(2δ)` and 31.10.19 (all solutions of 31.10.18) violate
  31.10.14 (residuals `2.7·10⁻⁴`, `10⁻²`); with `u = (stz/a)^{1/2}` all three satisfy it to
  `10⁻³²`. (Only with this `u` is `u² + v² + w²` free of the cubic term `stz`.)
* **31.10.22–31.10.23**: the printed P-symbol `P{0,1,∞; 0,0,a; ½(3-γ), c, b; cos²θ}` violates
  Fuchs's relation (the exponents sum to `γ/2`, not `1`) and the printed separable kernel does
  not satisfy 31.10.21 (residual `1.23`). The corrected data, derived from the indicial
  equations of 31.10.21 and checked numerically (residual `3·10⁻³⁰`), are: exponent `1 - γ`
  (not `½(3-γ)`) at `0`; `p² + (α+β-γ)p - σ₂/4 = 0`; `a + b = α + β + 2p`;
  `ab = p² + (α+β)p - σ₁/4`; `c = γ - α - β - 2p`; the other relations of 31.10.23 are correct.
* **§31.10(i), Example 2**: the Fuchs–Frobenius solution at `∞` with exponent `α` is
  `z^{-α} Hl(1/a, q_m/a - α(β-ε) - (α/a)(β-δ); α, α-γ+1, α-β+1, δ; 1/z)` (31.3.10), not
  `z^{-α} Hl(1/a, q_m; …)` as printed: the printed function is not a solution of Heun's equation
  with accessory parameter `q_m` (ODE residual `2.9·10⁻³` at `z = 5 + 3i`). The representation
  itself is not acquired (along the contour the kernel's `₂F₁(…; a/(zt))` must be continued
  beyond its disk of convergence); its kernel equation is `heun_kernel_example₂_pde`.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology Real

noncomputable section

namespace DLMF.Heun

variable {a q α β γ δ ε : ℂ}

/-! ### Solutions via quadratures (§31.8) -/

/-- DLMF 31.8.1–31.8.3: for half-odd-integer exponent parameters `β - α = m₀ + 1/2`,
`γ = -m₁ + 1/2`, `δ = -m₂ + 1/2`, `ε = -m₃ + 1/2` (`m_k ∈ ℕ`), with `N = m₀ + m₁ + m₂ + m₃` and
`g = ½ max(2 max m_k, 1 + N - (1 + (-1)^N)(1/2 + min m_k))`, there are a polynomial
`Ψ(λ, z)` of degree `g` in `λ` and `N` in `z` and a spectral polynomial `P(λ)` of degree
`2g + 1` (the curve `Γ : ν² = P(λ)`) such that for every `λ = -4q`: `z ↦ Ψ(λ, z)` solves the
third-order equation for products of two solutions of Heun's equation, and for `ν² = P(λ)` the
functions `w_± = √Ψ exp(±(iν/2) ∫ t^{m₁}(t-1)^{m₂}(t-a)^{m₃}/(Ψ √(t(t-1)(t-a))) dt)` (31.8.2)
solve Heun's equation, for any analytic branches of the square roots and of the primitive on an
open set. Stated for natural indices `m_k`. -/
@[dlmf 31.8.E1, dlmf 31.8.E2, dlmf 31.8.E3]
theorem heun_hermiteDarboux (ha0 : a ≠ 0) (ha1 : a ≠ 1) (m : Fin 4 → ℕ)
    (hβα : β - α = m 0 + 1 / 2) (hγ : γ = -(m 1 : ℂ) + 1 / 2) (hδ : δ = -(m 2 : ℂ) + 1 / 2)
    (hε : ε = -(m 3 : ℂ) + 1 / 2) (hF : α + β + 1 = γ + δ + ε) :
    let N := m 0 + m 1 + m 2 + m 3
    let g := max (max (max (m 0) (m 1)) (max (m 2) (m 3)))
      (if Even N then N / 2 - min (min (m 0) (m 1)) (min (m 2) (m 3)) else (N + 1) / 2)
    ∃ (Ψ : Polynomial (Polynomial ℂ)) (P : Polynomial ℂ),
      Ψ.natDegree = N ∧ (∀ i, (Ψ.coeff i).natDegree ≤ g) ∧ P.natDegree = 2 * g + 1 ∧
      ∀ (lam : ℂ), let ψ : ℂ → ℂ := fun z => (Ψ.map (Polynomial.evalRingHom lam)).eval z
        let p := heunCoeffP a γ δ ε
        let r := heunCoeffR a (-lam / 4) α β
        (∀ z, z ≠ 0 → z ≠ 1 → z ≠ a →
          iteratedDeriv 3 ψ z + 3 * p z * iteratedDeriv 2 ψ z +
            (2 * p z ^ 2 + deriv p z + 4 * r z) * deriv ψ z +
            (4 * p z * r z + 2 * deriv r z) * ψ z = 0) ∧
        ∀ (ν : ℂ), ν ^ 2 = P.eval lam →
          ∀ (U : Set ℂ) (S R G : ℂ → ℂ), IsOpen U → (∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a) →
            (∀ z ∈ U, S z ^ 2 = ψ z ∧ R z ^ 2 = z * (z - 1) * (z - a) ∧ ψ z ≠ 0) →
            AnalyticOnNhd ℂ S U → AnalyticOnNhd ℂ R U →
            (∀ z ∈ U, HasDerivAt G (z ^ m 1 * (z - 1) ^ m 2 * (z - a) ^ m 3 / (ψ z * R z)) z) →
            IsHeunSolOn a (-lam / 4) α β γ δ ε (fun z => S z * cexp (I * ν / 2 * G z)) U ∧
            IsHeunSolOn a (-lam / 4) α β γ δ ε (fun z => S z * cexp (-(I * ν / 2 * G z))) U := by
  sorry

/-- DLMF 31.8.4: for `𝐦 = (1, 1, 0, 0)` (so `α = -1`, `β = 1/2`, `γ = -1/2`, `δ = ε = 1/2`),
`Ψ_{1,2} = z² + λz + a` and `ν² = (λ + a + 1)(λ² - 4a)`: the functions 31.8.2 solve Heun's
equation with `q = -λ/4`, for any analytic branches on an open set. -/
@[dlmf 31.8.E4, dlmf 31.8.E2]
theorem heun_hermiteDarboux_example₁ (ha0 : a ≠ 0) (ha1 : a ≠ 1) {lam ν : ℂ}
    (hν : ν ^ 2 = (lam + a + 1) * (lam ^ 2 - 4 * a)) {U : Set ℂ} (hU : IsOpen U)
    (hUs : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a ∧ z ^ 2 + lam * z + a ≠ 0) {S R G : ℂ → ℂ}
    (hS : ∀ z ∈ U, S z ^ 2 = z ^ 2 + lam * z + a) (hR : ∀ z ∈ U, R z ^ 2 = z * (z - 1) * (z - a))
    (hSa : AnalyticOnNhd ℂ S U) (hRa : AnalyticOnNhd ℂ R U)
    (hG : ∀ z ∈ U, HasDerivAt G (z / ((z ^ 2 + lam * z + a) * R z)) z) (s : ℂ)
    (hs : s = 1 ∨ s = -1) :
    IsHeunSolOn a (-lam / 4) (-1) (1 / 2) (-1 / 2) (1 / 2) (1 / 2)
      (fun z => S z * cexp (s * (I * ν / 2) * G z)) U := by
  sorry

/-- DLMF 31.8.5 (as corrected in DLMF 1.0.7): for `𝐦 = (1, -2, 0, 0)` (so `α = 1/2`, `β = 2`,
`γ = 5/2`, `δ = ε = 1/2`), `Ψ_{1,-1} = (z² + (λ + 3a + 3)z + a)/z³` and
`ν² = (λ + 4a + 4)((λ + 3a + 3)² - 4a)`: the functions 31.8.2 (with `t^{m₁} = t^{-2}`) solve
Heun's equation with `q = -λ/4`. -/
@[dlmf 31.8.E5, dlmf 31.8.E2]
theorem heun_hermiteDarboux_example₂ (ha0 : a ≠ 0) (ha1 : a ≠ 1) {lam ν : ℂ}
    (hν : ν ^ 2 = (lam + 4 * a + 4) * ((lam + 3 * a + 3) ^ 2 - 4 * a)) {U : Set ℂ}
    (hU : IsOpen U)
    (hUs : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a ∧ z ^ 2 + (lam + 3 * a + 3) * z + a ≠ 0)
    {S R G : ℂ → ℂ} (hS : ∀ z ∈ U, S z ^ 2 = (z ^ 2 + (lam + 3 * a + 3) * z + a) / z ^ 3)
    (hR : ∀ z ∈ U, R z ^ 2 = z * (z - 1) * (z - a))
    (hSa : AnalyticOnNhd ℂ S U) (hRa : AnalyticOnNhd ℂ R U)
    (hG : ∀ z ∈ U, HasDerivAt G
      (z⁻¹ ^ 2 / ((z ^ 2 + (lam + 3 * a + 3) * z + a) / z ^ 3 * R z)) z) (s : ℂ)
    (hs : s = 1 ∨ s = -1) :
    IsHeunSolOn a (-lam / 4) (1 / 2) 2 (5 / 2) (1 / 2) (1 / 2)
      (fun z => S z * cexp (s * (I * ν / 2) * G z)) U := by
  sorry

/-! ### Type I integral equations (§31.10(i)) -/

/-- DLMF 31.10.1–31.10.6: if `w` solves Heun's equation on `V`, the kernel `𝒦(z, t)` solves
`(𝒟_z - 𝒟_t)𝒦 = 0` (31.10.3, Heun's operator 31.10.4), `ρ` is a branch on `V` of the weight
`t^{γ-1}(t-1)^{δ-1}(t-a)^{ε-1}` (31.10.2, given by its logarithmic derivative), and the
contour `C` (a `C¹` path in `V`) is such that the concomitant
`p(t)(∂𝒦/∂t w(t) - 𝒦 dw/dt)`, `p(t) = t(t-1)(t-a)ρ(t)` (31.10.5–31.10.6), takes equal values at
the two ends, then `W(z) = ∫_C 𝒦(z, t) w(t) ρ(t) dt` (31.10.1) is a solution of Heun's
equation. -/
@[dlmf 31.10.E1, dlmf 31.10.E2, dlmf 31.10.E3, dlmf 31.10.E5, dlmf 31.10.E6]
theorem heun_integral_typeI (hF : α + β + 1 = γ + δ + ε) {U V : Set ℂ} (hU : IsOpen U)
    (hV : IsOpen V) (hUs : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a)
    (hVs : ∀ t ∈ V, t ≠ 0 ∧ t ≠ 1 ∧ t ≠ a) {w ρ : ℂ → ℂ} {K : ℂ → ℂ → ℂ} {C : ℝ → ℂ}
    (hw : IsHeunSolOn a q α β γ δ ε w V)
    (hρ : ∀ t ∈ V, HasDerivAt ρ (ρ t * ((γ - 1) / t + (δ - 1) / (t - 1) + (ε - 1) / (t - a))) t)
    (hK : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => K x.1 x.2) (U ×ˢ V))
    (hKpde : ∀ z ∈ U, ∀ t ∈ V,
      heunOperator a α β γ δ ε (fun z' => K z' t) z = heunOperator a α β γ δ ε (K z) t)
    (hC : ContDiffOn ℝ 1 C (Icc 0 1)) (hCV : ∀ s ∈ Icc (0 : ℝ) 1, C s ∈ V)
    (hbd : ∀ z ∈ U,
      C 1 * (C 1 - 1) * (C 1 - a) * ρ (C 1) * (deriv (K z) (C 1) * w (C 1) -
          K z (C 1) * deriv w (C 1)) =
        C 0 * (C 0 - 1) * (C 0 - a) * ρ (C 0) * (deriv (K z) (C 0) * w (C 0) -
          K z (C 0) * deriv w (C 0))) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => ∫ s in (0 : ℝ)..1, K z (C s) * w (C s) * ρ (C s) * deriv C s) U := by
  sorry

/-- DLMF 31.10.7–31.10.8 (**31.10.8 sign corrected**): with
`cos²θ = zt/a`, `sin²θ cos²φ = -(z-a)(t-a)/(a(1-a))`, `sin²θ sin²φ = (z-1)(t-1)/(1-a)`
(31.10.7 squared), a kernel `𝒦(z, t)` with `(𝒟_z - 𝒟_t)𝒦 = 0` satisfies, as a function of
`(θ, φ)`, `sin²θ(𝒦_θθ + ((1-2γ)tan θ + 2(δ+ε-1/2)cot θ)𝒦_θ - 4αβ𝒦) + 𝒦_φφ
+ ((2δ-1)cot φ - (2ε-1)tan φ)𝒦_φ = 0`. Stated for analytic `Z, T` of `(θ, φ)` satisfying the
relations on an open set where the change of variables is valid. -/
@[dlmf 31.10.E7, dlmf 31.10.E8]
theorem heun_kernel_typeI_angles (hF : α + β + 1 = γ + δ + ε) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω) {Z T : ℂ → ℂ → ℂ} {K : ℂ → ℂ → ℂ}
    (hZT : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => (Z x.1 x.2, T x.1 x.2)) Ω)
    (hrel : ∀ x ∈ Ω, Z x.1 x.2 * T x.1 x.2 = a * Complex.cos x.1 ^ 2 ∧
      (Z x.1 x.2 - 1) * (T x.1 x.2 - 1) = (1 - a) * Complex.sin x.1 ^ 2 * Complex.sin x.2 ^ 2 ∧
      (Z x.1 x.2 - a) * (T x.1 x.2 - a) = -(a * (1 - a)) * Complex.sin x.1 ^ 2 *
        Complex.cos x.2 ^ 2)
    (hreg : ∀ x ∈ Ω, Z x.1 x.2 ≠ T x.1 x.2 ∧ Complex.sin x.1 ≠ 0 ∧ Complex.cos x.1 ≠ 0 ∧
      Complex.sin x.2 ≠ 0 ∧ Complex.cos x.2 ≠ 0)
    (hK : AnalyticOnNhd ℂ (fun y : ℂ × ℂ => K y.1 y.2)
      ((fun x : ℂ × ℂ => (Z x.1 x.2, T x.1 x.2)) '' Ω))
    (hKpde : ∀ x ∈ Ω, heunOperator a α β γ δ ε (fun z' => K z' (T x.1 x.2)) (Z x.1 x.2) =
      heunOperator a α β γ δ ε (K (Z x.1 x.2)) (T x.1 x.2)) :
    ∀ x ∈ Ω, let 𝒦 : ℂ → ℂ → ℂ := fun θ φ => K (Z θ φ) (T θ φ)
      Complex.sin x.1 ^ 2 * (deriv (deriv fun θ => 𝒦 θ x.2) x.1 +
          ((1 - 2 * γ) * Complex.tan x.1 + 2 * (δ + ε - 1 / 2) * Complex.cot x.1) *
            deriv (fun θ => 𝒦 θ x.2) x.1 - 4 * α * β * 𝒦 x.1 x.2) +
        deriv (deriv (𝒦 x.1)) x.2 +
        ((2 * δ - 1) * Complex.cot x.2 - (2 * ε - 1) * Complex.tan x.2) * deriv (𝒦 x.1) x.2 =
        0 := by
  sorry

/-- DLMF 31.10.9: the separable solutions of the (corrected) kernel equation 31.10.8:
`𝒦(θ, φ) = f(cos²θ) g(cos²φ)` with `f ∈ P{0, 1, ∞; 0, 1/2-δ-σ, α; 1-γ, 1/2-ε+σ, β; ·}` and
`g ∈ P{0, 1, ∞; 0, 0, -1/2+δ+σ; 1-ε, 1-δ, -1/2+ε-σ; ·}` (Riemann's equation,
`riemannNormalOperator`), `σ` a separation constant. -/
@[dlmf 31.10.E9, dlmf 31.10.E8]
theorem heun_kernel_typeI_separable (hF : α + β + 1 = γ + δ + ε) (σ : ℂ) {f g : ℂ → ℂ}
    {Uf Ug : Set ℂ} (hUf : IsOpen Uf) (hUg : IsOpen Ug)
    (hf : ContDiffOn ℂ 2 f Uf ∧ ∀ x ∈ Uf, DLMF.Hypergeometric.riemannNormalOperator 0 (1 - γ)
      (1 / 2 - δ - σ) (1 / 2 - ε + σ) α β f x = 0)
    (hg : ContDiffOn ℂ 2 g Ug ∧ ∀ y ∈ Ug, DLMF.Hypergeometric.riemannNormalOperator 0 (1 - ε) 0
      (1 - δ) (-1 / 2 + δ + σ) (-1 / 2 + ε - σ) g y = 0)
    {θ φ : ℂ} (hθ : Complex.cos θ ^ 2 ∈ Uf) (hφ : Complex.cos φ ^ 2 ∈ Ug)
    (hreg : Complex.sin θ ≠ 0 ∧ Complex.cos θ ≠ 0 ∧ Complex.sin φ ≠ 0 ∧ Complex.cos φ ≠ 0) :
    let 𝒦 : ℂ → ℂ → ℂ := fun θ φ => f (Complex.cos θ ^ 2) * g (Complex.cos φ ^ 2)
    Complex.sin θ ^ 2 * (deriv (deriv fun θ' => 𝒦 θ' φ) θ +
        ((1 - 2 * γ) * Complex.tan θ + 2 * (δ + ε - 1 / 2) * Complex.cot θ) *
          deriv (fun θ' => 𝒦 θ' φ) θ - 4 * α * β * 𝒦 θ φ) +
      deriv (deriv (𝒦 θ)) φ +
      ((2 * δ - 1) * Complex.cot φ - (2 * ε - 1) * Complex.tan φ) * deriv (𝒦 θ) φ = 0 := by
  sorry

/-- DLMF 31.10.10 (Example 1): the kernel
`𝒦(z, t) = (zt - a)^{1/2-δ-σ} ₂F₁(1/2-δ-σ+α, 1/2-δ-σ+β; γ; zt/a)
₂F₁(-1/2+δ+σ, -1/2+ε-σ; δ; a(z-1)(t-1)/((a-1)(zt-a)))` satisfies `(𝒟_z - 𝒟_t)𝒦 = 0`
(31.10.3) where both hypergeometric series converge and `zt - a ∈ slitPlane`. -/
@[dlmf 31.10.E10, dlmf 31.10.E3]
theorem heun_kernel_example₁_pde (hF : α + β + 1 = γ + δ + ε) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (σ : ℂ) {z t : ℂ}
    (hzt : ‖z * t / a‖ < 1 ∧ ‖a * (z - 1) * (t - 1) / ((a - 1) * (z * t - a))‖ < 1 ∧
      z * t - a ∈ slitPlane) :
    let K : ℂ → ℂ → ℂ := fun z t => (z * t - a) ^ (1 / 2 - δ - σ) *
      ordinaryHypergeometric (1 / 2 - δ - σ + α) (1 / 2 - δ - σ + β) γ (z * t / a) *
      ordinaryHypergeometric (-1 / 2 + δ + σ) (-1 / 2 + ε - σ) δ
        (a * (z - 1) * (t - 1) / ((a - 1) * (z * t - a)))
    heunOperator a α β γ δ ε (fun z' => K z' t) z = heunOperator a α β γ δ ε (K z) t := by
  sorry

/-- DLMF §31.10(i), Example 1: for `ℜγ > 0`, `ℜδ > 0`, an eigenvalue `q_m` (pair `(0, 1)`) and
`C` the Pochhammer loop `(1+, 0+, 1-, 0-)` based at `ζ ∈ (0, 1)`, the Heun function
`w_m = (0,1)Hf_m` satisfies the integral equation
`κ_m w_m(z) = ∫_C 𝒦(z, t) w_m(t) ρ(t) dt` with the kernel 31.10.10, for some eigenvalue `κ_m` and
all `z` near `ζ` (branches continued along `C`, principal at the start). -/
@[dlmf 31.10.E10, dlmf 31.10.E1]
theorem heun_integralEquation_example₁ (hF : α + β + 1 = γ + δ + ε) (ha : 1 < ‖a‖)
    (hγ : 0 < γ.re) (hδ : 0 < δ.re) (σ : ℂ) {ζ : ℝ} (hζ : ζ ∈ Ioo (0 : ℝ) 1)
    (ha1 : 1 - ζ < ‖a - 1‖) (hε : ε = heunEps α β γ δ) {qm : ℂ}
    (hm : IsHeunEigenvalue01 a qm α β γ δ) :
    ∃ κ : ℂ, ∀ᶠ z in 𝓝 (ζ : ℂ),
      continuedPathIntegral (pochhammerLoop 0 1 ζ)
        (fun t => (z * t - a) ^ (1 / 2 - δ - σ) *
          ordinaryHypergeometric (1 / 2 - δ - σ + α) (1 / 2 - δ - σ + β) γ (z * t / a) *
          ordinaryHypergeometric (-1 / 2 + δ + σ) (-1 / 2 + ε - σ) δ
            (a * (z - 1) * (t - 1) / ((a - 1) * (z * t - a))) *
          heunLocal a qm α β γ δ t * localBranchCpow ζ (γ - 1) t *
          localBranchCpow (ζ - 1) (δ - 1) (t - 1) * localBranchCpow (ζ - a) (ε - 1) (t - a)) =
        κ * heunLocal a qm α β γ δ z := by
  sorry

/-- DLMF 31.10.11 (Example 2): the kernel
`𝒦(z, t) = (zt - a)^{1/2-δ-σ} (zt/a)^{-1/2+δ+σ-α}
₂F₁(1/2-δ-σ+α, 3/2-δ-σ+α-γ; α-β+1; a/(zt)) · g((z-a)(t-a)/((1-a)(zt-a)))` with `g` the
branch `₂F₁(-1/2+δ+σ, -1/2+ε-σ; ε; ·)` (exponent `0` at `0`) of the P-symbol
`P{0, 1, ∞; 0, 0, -1/2+δ+σ; 1-ε, 1-δ, -1/2+ε-σ; ·}` satisfies `(𝒟_z - 𝒟_t)𝒦 = 0`, where the
series converge and the power bases are in `slitPlane`. -/
@[dlmf 31.10.E11, dlmf 31.10.E3]
theorem heun_kernel_example₂_pde (hF : α + β + 1 = γ + δ + ε) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (σ : ℂ) {z t : ℂ}
    (hzt : ‖a / (z * t)‖ < 1 ∧ ‖(z - a) * (t - a) / ((1 - a) * (z * t - a))‖ < 1 ∧
      z * t - a ∈ slitPlane ∧ z * t / a ∈ slitPlane) :
    let K : ℂ → ℂ → ℂ := fun z t => (z * t - a) ^ (1 / 2 - δ - σ) *
      (z * t / a) ^ (-1 / 2 + δ + σ - α) *
      ordinaryHypergeometric (1 / 2 - δ - σ + α) (3 / 2 - δ - σ + α - γ) (α - β + 1)
        (a / (z * t)) *
      ordinaryHypergeometric (-1 / 2 + δ + σ) (-1 / 2 + ε - σ) ε
        ((z - a) * (t - a) / ((1 - a) * (z * t - a)))
    heunOperator a α β γ δ ε (fun z' => K z' t) z = heunOperator a α β γ δ ε (K z) t := by
  sorry

/-! ### Type II integral equations (§31.10(ii)) -/

/-- DLMF 31.10.12–31.10.16: if `w` solves Heun's equation on `V`, `ρ₁` is a branch on `V` of
`t^{γ-1}(1-t)^{δ-1}(1-t/a)^{ε-1}` (given by its logarithmic derivative), so that
`ρ(s, t) = (s - t) ρ₁(s) ρ₁(t)` is the weight 31.10.13, the kernel `𝒦(z; s, t)` satisfies
`((t-z)𝒟_s + (z-s)𝒟_t + (s-t)𝒟_z)𝒦 = 0` (31.10.14), and the concomitants
`p(t)(∂_t𝒦 w(t) - 𝒦 w'(t))` along `C₂` and `p(s)(∂_s𝒦 w(s) - 𝒦 w'(s))` along `C₁` take equal
values at the ends of the paths (31.10.15–31.10.16, `p(t) = t(t-1)(t-a)ρ₁(t)` up to a constant
factor), then `W(z) = ∫_{C₁}∫_{C₂} 𝒦(z; s, t) w(s) w(t) ρ(s, t) dt ds` (31.10.12, `s` along
`C₁`, `t` along `C₂`) is a solution of Heun's equation. -/
@[dlmf 31.10.E12, dlmf 31.10.E13, dlmf 31.10.E14, dlmf 31.10.E15, dlmf 31.10.E16]
theorem heun_integral_typeII (hF : α + β + 1 = γ + δ + ε) {U V : Set ℂ} (hU : IsOpen U)
    (hV : IsOpen V) (hUs : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a)
    (hVs : ∀ t ∈ V, t ≠ 0 ∧ t ≠ 1 ∧ t ≠ a) {w ρ₁ : ℂ → ℂ} {K : ℂ → ℂ → ℂ → ℂ}
    {C₁ C₂ : ℝ → ℂ} (hw : IsHeunSolOn a q α β γ δ ε w V)
    (hρ : ∀ t ∈ V, HasDerivAt ρ₁ (ρ₁ t * ((γ - 1) / t + (δ - 1) / (t - 1) + (ε - 1) / (t - a))) t)
    (hK : AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => K x.1 x.2.1 x.2.2) (U ×ˢ V ×ˢ V))
    (hKpde : ∀ z ∈ U, ∀ s ∈ V, ∀ t ∈ V,
      (t - z) * heunOperator a α β γ δ ε (fun s' => K z s' t) s +
        (z - s) * heunOperator a α β γ δ ε (K z s) t +
        (s - t) * heunOperator a α β γ δ ε (fun z' => K z' s t) z = 0)
    (hC₁ : ContDiffOn ℝ 1 C₁ (Icc 0 1)) (hC₂ : ContDiffOn ℝ 1 C₂ (Icc 0 1))
    (hC₁V : ∀ x ∈ Icc (0 : ℝ) 1, C₁ x ∈ V) (hC₂V : ∀ x ∈ Icc (0 : ℝ) 1, C₂ x ∈ V)
    (hbd₂ : ∀ z ∈ U, ∀ s ∈ V, let B : ℂ → ℂ := fun t => t * (t - 1) * (t - a) * ρ₁ t *
        (deriv (K z s) t * w t - K z s t * deriv w t)
      B (C₂ 1) = B (C₂ 0))
    (hbd₁ : ∀ z ∈ U, ∀ t ∈ V, let B : ℂ → ℂ := fun s => s * (s - 1) * (s - a) * ρ₁ s *
        (deriv (fun s' => K z s' t) s * w s - K z s t * deriv w s)
      B (C₁ 1) = B (C₁ 0)) :
    IsHeunSolOn a q α β γ δ ε
      (fun z => ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        K z (C₁ x) (C₂ y) * w (C₁ x) * w (C₂ y) * ((C₁ x - C₂ y) * ρ₁ (C₁ x) * ρ₁ (C₂ y)) *
          deriv C₁ x * deriv C₂ y) U := by
  sorry

/-- DLMF 31.10.17–31.10.18 (**31.10.17 corrected**: `u = (stz/a)^{1/2}`): with
`u = (stz/a)^{1/2}`, `v = ((s-1)(t-1)(z-1)/(1-a))^{1/2}`, `w = i((s-a)(t-a)(z-a)/(a(1-a)))^{1/2}`
(principal roots), a function `𝒦(u, v, w)` with
`𝒦_uu + 𝒦_vv + 𝒦_ww + ((2γ-1)/u)𝒦_u + ((2δ-1)/v)𝒦_v + ((2ε-1)/w)𝒦_w = 0` (31.10.18) gives a
kernel `𝒦(u, v, w)` satisfying 31.10.14, at points where the roots are analytic and nonzero. -/
@[dlmf 31.10.E17, dlmf 31.10.E18, dlmf 31.10.E14]
theorem heun_kernel_typeII_uvw (hF : α + β + 1 = γ + δ + ε) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    {Ω : Set (ℂ × ℂ × ℂ)} (hΩ : IsOpen Ω) {𝒦 : ℂ → ℂ → ℂ → ℂ}
    (h𝒦 : AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => 𝒦 x.1 x.2.1 x.2.2) Ω)
    (hpde : ∀ x ∈ Ω, let u := x.1; let v := x.2.1; let w := x.2.2
      deriv (deriv fun u' => 𝒦 u' v w) u + deriv (deriv fun v' => 𝒦 u v' w) v +
        deriv (deriv (𝒦 u v)) w + (2 * γ - 1) / u * deriv (fun u' => 𝒦 u' v w) u +
        (2 * δ - 1) / v * deriv (fun v' => 𝒦 u v' w) v +
        (2 * ε - 1) / w * deriv (𝒦 u v) w = 0)
    {z s t : ℂ}
    (hpt : s * t * z / a ∈ slitPlane ∧ (s - 1) * (t - 1) * (z - 1) / (1 - a) ∈ slitPlane ∧
      (s - a) * (t - a) * (z - a) / (a * (1 - a)) ∈ slitPlane)
    (hΩpt : ((s * t * z / a) ^ (1 / 2 : ℂ), ((s - 1) * (t - 1) * (z - 1) / (1 - a)) ^ (1 / 2 : ℂ),
      I * ((s - a) * (t - a) * (z - a) / (a * (1 - a))) ^ (1 / 2 : ℂ)) ∈ Ω) :
    let K : ℂ → ℂ → ℂ → ℂ := fun z s t => 𝒦 ((s * t * z / a) ^ (1 / 2 : ℂ))
      (((s - 1) * (t - 1) * (z - 1) / (1 - a)) ^ (1 / 2 : ℂ))
      (I * ((s - a) * (t - a) * (z - a) / (a * (1 - a))) ^ (1 / 2 : ℂ))
    (t - z) * heunOperator a α β γ δ ε (fun s' => K z s' t) s +
      (z - s) * heunOperator a α β γ δ ε (K z s) t +
      (s - t) * heunOperator a α β γ δ ε (fun z' => K z' s t) z = 0 := by
  sorry

/-- DLMF 31.10.19: products of cylinder functions solve the kernel equation 31.10.18:
`𝒦 = u^{1-γ} v^{1-δ} w^{1-ε} 𝒞_{1-γ}(u√σ₁) 𝒞_{1-δ}(v√σ₂) 𝒞_{1-ε}(iw√(σ₁+σ₂))`, where each
`𝒞_ν` is any solution of Bessel's equation `𝒞'' + 𝒞'/x + (1 - ν²/x²)𝒞 = 0` (§10.2(ii)),
`σ₁, σ₂` separation constants (principal powers and roots, at points off the branch cuts). -/
@[dlmf 31.10.E19, dlmf 31.10.E18]
theorem heun_kernel_typeII_cylinder (σ₁ σ₂ : ℂ) {C₁ C₂ C₃ : ℂ → ℂ} {S₁ S₂ S₃ : Set ℂ}
    (h₁ : IsLinearODE2On (fun x => 1 / x) (fun x => 1 - (1 - γ) ^ 2 / x ^ 2) C₁ S₁)
    (h₂ : IsLinearODE2On (fun x => 1 / x) (fun x => 1 - (1 - δ) ^ 2 / x ^ 2) C₂ S₂)
    (h₃ : IsLinearODE2On (fun x => 1 / x) (fun x => 1 - (1 - ε) ^ 2 / x ^ 2) C₃ S₃)
    (hS : IsOpen S₁ ∧ IsOpen S₂ ∧ IsOpen S₃) {u v w : ℂ}
    (hu : u ∈ slitPlane ∧ u * σ₁ ^ (1 / 2 : ℂ) ∈ S₁)
    (hv : v ∈ slitPlane ∧ v * σ₂ ^ (1 / 2 : ℂ) ∈ S₂)
    (hw : w ∈ slitPlane ∧ I * w * (σ₁ + σ₂) ^ (1 / 2 : ℂ) ∈ S₃)
    (hσ : σ₁ ≠ 0 ∧ σ₂ ≠ 0 ∧ σ₁ + σ₂ ≠ 0) :
    let 𝒦 : ℂ → ℂ → ℂ → ℂ := fun u v w => u ^ (1 - γ) * v ^ (1 - δ) * w ^ (1 - ε) *
      C₁ (u * σ₁ ^ (1 / 2 : ℂ)) * C₂ (v * σ₂ ^ (1 / 2 : ℂ)) *
      C₃ (I * w * (σ₁ + σ₂) ^ (1 / 2 : ℂ))
    deriv (deriv fun u' => 𝒦 u' v w) u + deriv (deriv fun v' => 𝒦 u v' w) v +
      deriv (deriv (𝒦 u v)) w + (2 * γ - 1) / u * deriv (fun u' => 𝒦 u' v w) u +
      (2 * δ - 1) / v * deriv (fun v' => 𝒦 u v' w) v +
      (2 * ε - 1) / w * deriv (𝒦 u v) w = 0 := by
  sorry

/-- DLMF 31.10.20–31.10.21: in spherical coordinates `u = r cos θ`, `v = r sin θ sin φ`,
`w = r sin θ cos φ`, a solution of 31.10.18 satisfies
`𝒦_rr + ((2(γ+δ+ε)-1)/r)𝒦_r + 𝒦_θθ/r² + ((2(δ+ε)-1)cot θ - (2γ-1)tan θ)𝒦_θ/r²
+ 𝒦_φφ/(r² sin²θ) + ((2δ-1)cot φ - (2ε-1)tan φ)𝒦_φ/(r² sin²θ) = 0`. -/
@[dlmf 31.10.E20, dlmf 31.10.E21]
theorem heun_kernel_typeII_spherical {Ω : Set (ℂ × ℂ × ℂ)} (hΩ : IsOpen Ω)
    {𝒦 : ℂ → ℂ → ℂ → ℂ} (h𝒦 : AnalyticOnNhd ℂ (fun x : ℂ × ℂ × ℂ => 𝒦 x.1 x.2.1 x.2.2) Ω)
    (hpde : ∀ x ∈ Ω, let u := x.1; let v := x.2.1; let w := x.2.2
      deriv (deriv fun u' => 𝒦 u' v w) u + deriv (deriv fun v' => 𝒦 u v' w) v +
        deriv (deriv (𝒦 u v)) w + (2 * γ - 1) / u * deriv (fun u' => 𝒦 u' v w) u +
        (2 * δ - 1) / v * deriv (fun v' => 𝒦 u v' w) v +
        (2 * ε - 1) / w * deriv (𝒦 u v) w = 0)
    {r θ φ : ℂ} (hreg : r ≠ 0 ∧ Complex.sin θ ≠ 0 ∧ Complex.cos θ ≠ 0 ∧ Complex.sin φ ≠ 0 ∧
      Complex.cos φ ≠ 0)
    (hpt : ∀ᶠ y in 𝓝 (r, θ, φ), (y.1 * Complex.cos y.2.1,
      y.1 * Complex.sin y.2.1 * Complex.sin y.2.2,
      y.1 * Complex.sin y.2.1 * Complex.cos y.2.2) ∈ Ω) :
    let L : ℂ → ℂ → ℂ → ℂ := fun r θ φ =>
      𝒦 (r * Complex.cos θ) (r * Complex.sin θ * Complex.sin φ) (r * Complex.sin θ * Complex.cos φ)
    deriv (deriv fun r' => L r' θ φ) r + (2 * (γ + δ + ε) - 1) / r * deriv (fun r' => L r' θ φ) r +
      deriv (deriv fun θ' => L r θ' φ) θ / r ^ 2 +
      ((2 * (δ + ε) - 1) * Complex.cot θ - (2 * γ - 1) * Complex.tan θ) / r ^ 2 *
        deriv (fun θ' => L r θ' φ) θ +
      deriv (deriv (L r θ)) φ / (r ^ 2 * Complex.sin θ ^ 2) +
      ((2 * δ - 1) * Complex.cot φ - (2 * ε - 1) * Complex.tan φ) / (r ^ 2 * Complex.sin θ ^ 2) *
        deriv (L r θ) φ = 0 := by
  sorry

/-- DLMF 31.10.22–31.10.23 (**corrected**): separable solutions of 31.10.21,
`𝒦 = r^m sin^{2p}θ f(cos²θ) g(cos²φ)` with `f ∈ P{0, 1, ∞; 0, 0, A; 1-γ, c, B; ·}`,
`g ∈ P{0, 1, ∞; 0, 0, A'; 1-ε, 1-δ, B'; ·}` and `m² + 2(α+β)m - σ₁ = 0`,
`p² + (α+β-γ)p - σ₂/4 = 0`, `A + B = α + β + 2p`, `AB = p² + (α+β)p - σ₁/4`,
`c = γ - α - β - 2p`, `A' + B' = δ + ε - 1`, `A'B' = -σ₂/4`. DLMF prints the exponent `½(3-γ)`
for `1 - γ`, `p² + (α+β-γ-½)p - σ₂/4 = 0`, `A + B = 2(α+β+p) - 1`, `AB = p² - p(1-α-β) - σ₁/4`
and `c = γ - ½ - 2(α+β+p)`; see the module docstring. -/
@[dlmf 31.10.E22, dlmf 31.10.E23]
theorem heun_kernel_typeII_separable (hF : α + β + 1 = γ + δ + ε) {σ₁ σ₂ m p A B c A' B' : ℂ}
    (hm : m ^ 2 + 2 * (α + β) * m - σ₁ = 0) (hp : p ^ 2 + (α + β - γ) * p - σ₂ / 4 = 0)
    (hAB : A + B = α + β + 2 * p ∧ A * B = p ^ 2 + (α + β) * p - σ₁ / 4)
    (hc : c = γ - α - β - 2 * p) (hAB' : A' + B' = δ + ε - 1 ∧ A' * B' = -σ₂ / 4)
    {f g : ℂ → ℂ} {Uf Ug : Set ℂ} (hUf : IsOpen Uf) (hUg : IsOpen Ug)
    (hf : ContDiffOn ℂ 2 f Uf ∧ ∀ x ∈ Uf,
      DLMF.Hypergeometric.riemannNormalOperator 0 (1 - γ) 0 c A B f x = 0)
    (hg : ContDiffOn ℂ 2 g Ug ∧ ∀ y ∈ Ug,
      DLMF.Hypergeometric.riemannNormalOperator 0 (1 - ε) 0 (1 - δ) A' B' g y = 0)
    {r θ φ : ℂ} (hr : r ∈ slitPlane) (hθ : Complex.cos θ ^ 2 ∈ Uf ∧ Complex.sin θ ∈ slitPlane)
    (hφ : Complex.cos φ ^ 2 ∈ Ug)
    (hreg : Complex.sin θ ≠ 0 ∧ Complex.cos θ ≠ 0 ∧ Complex.sin φ ≠ 0 ∧ Complex.cos φ ≠ 0) :
    let L : ℂ → ℂ → ℂ → ℂ := fun r θ φ => r ^ m * Complex.sin θ ^ (2 * p) *
      f (Complex.cos θ ^ 2) * g (Complex.cos φ ^ 2)
    deriv (deriv fun r' => L r' θ φ) r + (2 * (γ + δ + ε) - 1) / r * deriv (fun r' => L r' θ φ) r +
      deriv (deriv fun θ' => L r θ' φ) θ / r ^ 2 +
      ((2 * (δ + ε) - 1) * Complex.cot θ - (2 * γ - 1) * Complex.tan θ) / r ^ 2 *
        deriv (fun θ' => L r θ' φ) θ +
      deriv (deriv (L r θ)) φ / (r ^ 2 * Complex.sin θ ^ 2) +
      ((2 * δ - 1) * Complex.cot φ - (2 * ε - 1) * Complex.tan φ) / (r ^ 2 * Complex.sin θ ^ 2) *
        deriv (L r θ) φ = 0 := by
  sorry

end DLMF.Heun
