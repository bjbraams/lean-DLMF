/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMF.Heun.Basic.Equation
public import DLMF.Heun.IntegralPath
public import DLMF.Heun.KernelAngles
public import DLMF.Hypergeometric.Riemann
public import DLMFMathlib.Analysis.Complex.BivariateCalculus
public import DLMFMathlib.Analysis.Calculus.Deriv.CompCurve
public import DLMFMathlib.MeasureTheory.Integral.PathParametric

/-!
# Solutions via quadratures, integral equations and representations (DLMF §31.8, §31.10)

## Main results

* `heun_hermiteDarboux`: finite-gap (Hermite–Darboux) solutions for half-odd-integer exponent
  parameters (31.8.1),
  `w_± = √Ψ exp(±(iν/2) ∫ t^{m₁}(t-1)^{m₂}(t-a)^{m₃}/(Ψ √(t(t-1)(t-a))) dt)` (31.8.2), with `Ψ`
  a polynomial solution of degree `g` in `λ = -4q` of the third-order equation for products of
  solutions (31.8.3).
* `heun_hermiteDarboux_example₁`, `heun_hermiteDarboux_example₂`: the examples 31.8.4–31.8.5.
* `heun_integral_typeI`: the Type I integral equation and representation, DLMF 31.10.1–31.10.6.
* `heun_kernel_typeI_angles`, `heun_kernel_typeI_separable`: the kernel equation in the
  variables 31.10.7 (31.10.8, sign corrected; from `heun_kernel_typeI_angles'` in
  `DLMF.Heun.KernelAngles`) and its separable solutions 31.10.9.
* `heun_kernel_example₁_pde`, `heun_integralEquation_example₁`, `heun_kernel_example₂_pde`:
  the kernels of Examples 1 and 2 (31.10.10, 31.10.11).
* `heun_integral_typeII`: the Type II double-integral representation, DLMF 31.10.12–31.10.16,
  from `heun_integral_typeII'` (in `DLMF.Heun.IntegralPath`).
* `heun_kernel_typeII_uvw`, `heun_kernel_typeII_cylinder`: the kernel equation in the variables
  31.10.17 (corrected) and 31.10.18, and its solutions 31.10.19 in cylinder functions.
* `heun_kernel_typeII_spherical`, `heun_kernel_typeII_separable`: the spherical form
  31.10.20–31.10.21 and its separable solutions 31.10.22–31.10.23 (corrected).
* `heun_integral_typeI'`: the Type I theorem without Fuchs's relation, by differentiation under
  the integral sign and the Lagrange identity `integral_heunOperator_comp_path`.
* `heun_kernel_typeII_uvw'`, `heun_kernel_typeII_spherical'`: the same changes of variables
  without the superfluous hypotheses; both are proved by the second-order chain rule for
  `(u, v, w) ↦ 𝒦(u, v, w)` along coordinate curves.

## Implementation notes

In §31.8 the square root and the integral are represented by arbitrary analytic branches
`S² = Ψ`, `G' = integrand` on an open set, so no branch choice is imposed. The remarks on
Hermite's Lamé solutions, the finite-gap property, the limit at the gap ends and Kovacic's
algorithm are not formalized.

The integral theorems of §31.10 are stated for a single-valued branch `ρ` of the weight on an
open set (any `ρ` with the logarithmic derivative of `t^{γ-1}(t-1)^{δ-1}(t-a)^{ε-1}`) and a `C¹`
path in that set, with the boundary terms 31.10.5 (31.10.15–31.10.16) equal at the two ends.
DLMF's Pochhammer-contour cases need continuation of the branches along the contour and are
covered only in the example statements via `continuedPathIntegral`.

Corrections to DLMF (numerical evidence with mpmath, complex parameters):

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
  itself is not formalized (along the contour the kernel's `₂F₁(…; a/(zt))` must be continued
  beyond its disk of convergence); its kernel equation is `heun_kernel_example₂_pde`.

Example 31.8.5 follows the correction of DLMF 1.0.7.
-/

@[expose] public section

open Complex Filter Set MeasureTheory
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

/-- Riccati form: if `w' = Λ w` and `Λ' + Λ² + pΛ + r = 0` on an open set, then `w` solves
`w'' + p w' + r w = 0` there. -/
private lemma isLinearODE2On_of_riccati {p r w Λ Λ' : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hw : ∀ z ∈ U, HasDerivAt w (Λ z * w z) z) (hΛ : ∀ z ∈ U, HasDerivAt Λ (Λ' z) z)
    (hR : ∀ z ∈ U, r z + p z * Λ z + Λ z ^ 2 + Λ' z = 0) : IsLinearODE2On p r w U := by
  have h1 : IsLinearODE2On (fun z => p z + 2 * Λ z) 0 (fun _ => (1 : ℂ)) U := by
    refine ⟨fun z _ => differentiableAt_const _, fun z _ => ?_⟩
    have : deriv (fun _ : ℂ => (1 : ℂ)) = fun _ => 0 := funext fun _ => deriv_const _ _
    rw [this]
    simpa using hasDerivAt_const z (0 : ℂ)
  have h := isLinearODE2On_gauge_mul (p := p) (r := r) hU hw hΛ (fun z _ => rfl)
    (fun z hz => by rw [Pi.zero_apply]; linear_combination -(hR z hz)) h1
  simpa using h

/-- Derivative of an analytic square root: if `S² = Ψ` near `z` and `S z ≠ 0`, then
`S' = Ψ'/(2S)`. -/
private lemma hasDerivAt_of_sq_eq {S Ψ : ℂ → ℂ} {Ψ' z : ℂ} {U : Set ℂ} (hU : IsOpen U) (hz : z ∈ U)
    (hS : ∀ x ∈ U, S x ^ 2 = Ψ x) (hSa : AnalyticAt ℂ S z) (hΨ : HasDerivAt Ψ Ψ' z)
    (hS0 : S z ≠ 0) : HasDerivAt S (Ψ' / (2 * S z)) z := by
  have hd := hSa.differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun x => S x ^ 2) (2 * S z * deriv S z) z := by
    convert hd.pow 2 using 1; ring
  have hev : (fun x => S x ^ 2) =ᶠ[𝓝 z] Ψ :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun x hx => hS x hx
  have h3 := h2.congr_of_eventuallyEq hev.symm
  have huniq := h3.unique hΨ
  convert hd using 1
  field_simp
  linear_combination -huniq

/-- DLMF 31.8.4: for `𝐦 = (1, 1, 0, 0)` (so `α = -1`, `β = 1/2`, `γ = -1/2`, `δ = ε = 1/2`),
`Ψ_{1,2} = z² + λz + a` and `ν² = (λ + a + 1)(λ² - 4a)`: the functions 31.8.2 solve Heun's
equation with `q = -λ/4`, for any analytic branches on an open set. -/
@[dlmf 31.8.E4, dlmf 31.8.E2]
theorem heun_hermiteDarboux_example₁ {lam ν : ℂ}
    (hν : ν ^ 2 = (lam + a + 1) * (lam ^ 2 - 4 * a)) {U : Set ℂ} (hU : IsOpen U)
    (hUs : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a ∧ z ^ 2 + lam * z + a ≠ 0) {S R G : ℂ → ℂ}
    (hS : ∀ z ∈ U, S z ^ 2 = z ^ 2 + lam * z + a) (hR : ∀ z ∈ U, R z ^ 2 = z * (z - 1) * (z - a))
    (hSa : AnalyticOnNhd ℂ S U) (hRa : AnalyticOnNhd ℂ R U)
    (hG : ∀ z ∈ U, HasDerivAt G (z / ((z ^ 2 + lam * z + a) * R z)) z) (s : ℂ)
    (hs : s = 1 ∨ s = -1) :
    IsHeunSolOn a (-lam / 4) (-1) (1 / 2) (-1 / 2) (1 / 2) (1 / 2)
      (fun z => S z * cexp (s * (I * ν / 2) * G z)) U := by
  have hc2 : (s * (I * ν / 2)) ^ 2 = -((lam + a + 1) * (lam ^ 2 - 4 * a)) / 4 := by
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    rw [mul_pow, div_pow, mul_pow, hs2, I_sq, hν]; ring
  generalize s * (I * ν / 2) = c at hc2 ⊢
  have hΨd : ∀ z, HasDerivAt (fun x : ℂ => x ^ 2 + lam * x + a) (2 * z + lam) z := fun z =>
    (((hasDerivAt_id z).pow 2).add ((hasDerivAt_id z).const_mul lam)).add_const a
      |>.congr_deriv (by simp)
  have hPd : ∀ z, HasDerivAt (fun x : ℂ => x * (x - 1) * (x - a))
      (3 * z ^ 2 - 2 * (1 + a) * z + a) z := fun z =>
    ((hasDerivAt_id z).mul ((hasDerivAt_id z).sub_const 1)).mul ((hasDerivAt_id z).sub_const a)
      |>.congr_deriv (by simp; ring)
  have hfacts : ∀ z ∈ U, z ≠ 0 ∧ z - 1 ≠ 0 ∧ z - a ≠ 0 ∧ z ^ 2 + lam * z + a ≠ 0 ∧
      R z ≠ 0 ∧ S z ≠ 0 := by
    intro z hz
    obtain ⟨h0, h1, h2, h3⟩ := hUs z hz
    have hP0 : z * (z - 1) * (z - a) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.2 h1)) (sub_ne_zero.2 h2)
    refine ⟨h0, sub_ne_zero.2 h1, sub_ne_zero.2 h2, h3, fun h => hP0 ?_, fun h => h3 ?_⟩
    · rw [← hR z hz, h]; ring
    · rw [← hS z hz, h]; ring
  refine isLinearODE2On_of_riccati
    (Λ := fun z => (2 * z + lam) / (2 * (z ^ 2 + lam * z + a)) + c * z /
      ((z ^ 2 + lam * z + a) * R z))
    (Λ' := fun z => (2 * (z ^ 2 + lam * z + a) - (2 * z + lam) ^ 2) /
        (2 * (z ^ 2 + lam * z + a) ^ 2) + c * z / ((z ^ 2 + lam * z + a) * R z) *
      (1 / z - (2 * z + lam) / (z ^ 2 + lam * z + a) -
        (3 * z ^ 2 - 2 * (1 + a) * z + a) / (2 * (z * (z - 1) * (z - a))))) hU
    (fun z hz => ?_) (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hfacts z hz
    have h3' : z * (z + lam) + a ≠ 0 := by convert h3 using 1; ring
    have hSd := hasDerivAt_of_sq_eq hU hz hS (hSa z hz) (hΨd z) h5
    have hEd := (((hG z hz).const_mul c)).cexp
    refine (hSd.mul hEd).congr_deriv ?_
    rw [← hS z hz]
    field_simp
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hfacts z hz
    have h3' : z * (z + lam) + a ≠ 0 := by convert h3 using 1; ring
    have hRd := hasDerivAt_of_sq_eq hU hz hR (hRa z hz) (hPd z) h4
    have hP0 : z * (z - 1) * (z - a) ≠ 0 := by rw [← hR z hz]; exact pow_ne_zero _ h4
    have hAd := ((((hasDerivAt_id z).const_mul 2).add_const lam).div ((hΨd z).const_mul 2)
        (mul_ne_zero two_ne_zero h3))
    have hBd := ((hasDerivAt_id z).const_mul c).div ((hΨd z).mul hRd) (mul_ne_zero h3 h4)
    refine (hAd.add hBd).congr_deriv ?_
    have hRz : R z ^ 2 = z * (z - 1) * (z - a) := hR z hz
    simp only [id, Pi.mul_apply]
    rw [← hRz]
    field_simp
    ring
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hfacts z hz
    have h3' : z * (z + lam) + a ≠ 0 := by convert h3 using 1; ring
    have hRz : R z ^ 2 = z * (z - 1) * (z - a) := hR z hz
    have hP0 : z * (z - 1) * (z - a) ≠ 0 := by rw [← hRz]; exact pow_ne_zero _ h4
    set B := c * z / ((z ^ 2 + lam * z + a) * R z) with hB
    have hB2 : B ^ 2 = c ^ 2 * z ^ 2 / ((z ^ 2 + lam * z + a) ^ 2 * (z * (z - 1) * (z - a))) := by
      rw [hB, div_pow, mul_pow, mul_pow (z ^ 2 + lam * z + a), hRz]
    have E1 : heunCoeffR a (-lam / 4) (-1) (1 / 2) z +
        heunCoeffP a (-1 / 2) (1 / 2) (1 / 2) z * ((2 * z + lam) / (2 * (z ^ 2 + lam * z + a))) +
        ((2 * z + lam) / (2 * (z ^ 2 + lam * z + a))) ^ 2 +
        (2 * (z ^ 2 + lam * z + a) - (2 * z + lam) ^ 2) / (2 * (z ^ 2 + lam * z + a) ^ 2) +
        c ^ 2 * z ^ 2 / ((z ^ 2 + lam * z + a) ^ 2 * (z * (z - 1) * (z - a))) = 0 := by
      rw [hc2]
      simp only [heunCoeffR, heunCoeffP]
      field_simp
      ring
    have E2 : heunCoeffP a (-1 / 2) (1 / 2) (1 / 2) z +
        2 * ((2 * z + lam) / (2 * (z ^ 2 + lam * z + a))) + 1 / z -
        (2 * z + lam) / (z ^ 2 + lam * z + a) -
        (3 * z ^ 2 - 2 * (1 + a) * z + a) / (2 * (z * (z - 1) * (z - a))) = 0 := by
      simp only [heunCoeffP]
      field_simp
      ring
    linear_combination E1 + B * E2 + hB2

/-- DLMF 31.8.5 (as corrected in DLMF 1.0.7): for `𝐦 = (1, -2, 0, 0)` (so `α = 1/2`, `β = 2`,
`γ = 5/2`, `δ = ε = 1/2`), `Ψ_{1,-1} = (z² + (λ + 3a + 3)z + a)/z³` and
`ν² = (λ + 4a + 4)((λ + 3a + 3)² - 4a)`: the functions 31.8.2 (with `t^{m₁} = t^{-2}`) solve
Heun's equation with `q = -λ/4`. -/
@[dlmf 31.8.E5, dlmf 31.8.E2]
theorem heun_hermiteDarboux_example₂ {lam ν : ℂ}
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
  have hc2 : (s * (I * ν / 2)) ^ 2 =
      -((lam + 4 * a + 4) * ((lam + 3 * a + 3) ^ 2 - 4 * a)) / 4 := by
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    rw [mul_pow, div_pow, mul_pow, hs2, I_sq, hν]; ring
  generalize s * (I * ν / 2) = c at hc2 ⊢
  set μ := lam + 3 * a + 3 with hμ
  have hQd : ∀ z, HasDerivAt (fun x : ℂ => x ^ 2 + μ * x + a) (2 * z + μ) z := fun z =>
    (((hasDerivAt_id z).pow 2).add ((hasDerivAt_id z).const_mul μ)).add_const a
      |>.congr_deriv (by simp)
  have hPd : ∀ z, HasDerivAt (fun x : ℂ => x * (x - 1) * (x - a))
      (3 * z ^ 2 - 2 * (1 + a) * z + a) z := fun z =>
    ((hasDerivAt_id z).mul ((hasDerivAt_id z).sub_const 1)).mul ((hasDerivAt_id z).sub_const a)
      |>.congr_deriv (by simp; ring)
  have hfacts : ∀ z ∈ U, z ≠ 0 ∧ z - 1 ≠ 0 ∧ z - a ≠ 0 ∧ z ^ 2 + μ * z + a ≠ 0 ∧
      R z ≠ 0 ∧ S z ≠ 0 := by
    intro z hz
    obtain ⟨h0, h1, h2, h3⟩ := hUs z hz
    have hP0 : z * (z - 1) * (z - a) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.2 h1)) (sub_ne_zero.2 h2)
    refine ⟨h0, sub_ne_zero.2 h1, sub_ne_zero.2 h2, h3, fun h => hP0 ?_, fun h => ?_⟩
    · rw [← hR z hz, h]; ring
    · have := hS z hz
      rw [h, zero_pow two_ne_zero, eq_comm, div_eq_zero_iff] at this
      rcases this with h' | h'
      · exact h3 h'
      · exact h0 (pow_eq_zero_iff three_ne_zero |>.1 h')
  have hΨd : ∀ z, z ≠ 0 → HasDerivAt (fun x : ℂ => (x ^ 2 + μ * x + a) / x ^ 3)
      ((2 * z + μ) / z ^ 3 - 3 * (z ^ 2 + μ * z + a) / z ^ 4) z := fun z hz0 =>
    ((hQd z).div ((hasDerivAt_id z).pow 3) (pow_ne_zero 3 hz0)).congr_deriv (by
      simp only [id, Pi.pow_apply]; field_simp; ring)
  refine isLinearODE2On_of_riccati
    (Λ := fun z => ((2 * z + μ) / (2 * (z ^ 2 + μ * z + a)) - 3 / (2 * z)) + c * z /
      ((z ^ 2 + μ * z + a) * R z))
    (Λ' := fun z => ((2 * (z ^ 2 + μ * z + a) - (2 * z + μ) ^ 2) /
        (2 * (z ^ 2 + μ * z + a) ^ 2) + 3 / (2 * z ^ 2)) + c * z / ((z ^ 2 + μ * z + a) * R z) *
      (1 / z - (2 * z + μ) / (z ^ 2 + μ * z + a) -
        (3 * z ^ 2 - 2 * (1 + a) * z + a) / (2 * (z * (z - 1) * (z - a))))) hU
    (fun z hz => ?_) (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hfacts z hz
    have h3' : z * (z + μ) + a ≠ 0 := by convert h3 using 1; ring
    have hSd := hasDerivAt_of_sq_eq hU hz hS (hSa z hz) (hΨd z h0) h5
    have hEd := (((hG z hz).const_mul c)).cexp
    refine (hSd.mul hEd).congr_deriv ?_
    have hSz := hS z hz
    have hS2 : (z ^ 2 + μ * z + a) = S z ^ 2 * z ^ 3 := by
      rw [hSz]; field_simp
    rw [hS2]
    field_simp
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hfacts z hz
    have h3' : z * (z + μ) + a ≠ 0 := by convert h3 using 1; ring
    have hRd := hasDerivAt_of_sq_eq hU hz hR (hRa z hz) (hPd z) h4
    have hP0 : z * (z - 1) * (z - a) ≠ 0 := by rw [← hR z hz]; exact pow_ne_zero _ h4
    have hAd := (((((hasDerivAt_id z).const_mul 2).add_const μ).div ((hQd z).const_mul 2)
        (mul_ne_zero two_ne_zero h3)).sub ((hasDerivAt_const z (3 : ℂ)).div
          ((hasDerivAt_id z).const_mul 2) (mul_ne_zero two_ne_zero h0)))
    have hBd := ((hasDerivAt_id z).const_mul c).div ((hQd z).mul hRd) (mul_ne_zero h3 h4)
    refine (hAd.add hBd).congr_deriv ?_
    have hRz : R z ^ 2 = z * (z - 1) * (z - a) := hR z hz
    simp only [id, Pi.mul_apply]
    rw [← hRz]
    field_simp
    ring
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hfacts z hz
    have h3' : z * (z + μ) + a ≠ 0 := by convert h3 using 1; ring
    have hRz : R z ^ 2 = z * (z - 1) * (z - a) := hR z hz
    have hP0 : z * (z - 1) * (z - a) ≠ 0 := by rw [← hRz]; exact pow_ne_zero _ h4
    set B := c * z / ((z ^ 2 + μ * z + a) * R z) with hB
    have hB2 : B ^ 2 = c ^ 2 * z ^ 2 / ((z ^ 2 + μ * z + a) ^ 2 * (z * (z - 1) * (z - a))) := by
      rw [hB, div_pow, mul_pow, mul_pow (z ^ 2 + μ * z + a), hRz]
    have E1 : heunCoeffR a (-lam / 4) (1 / 2) 2 z +
        heunCoeffP a (5 / 2) (1 / 2) (1 / 2) z *
          ((2 * z + μ) / (2 * (z ^ 2 + μ * z + a)) - 3 / (2 * z)) +
        ((2 * z + μ) / (2 * (z ^ 2 + μ * z + a)) - 3 / (2 * z)) ^ 2 +
        ((2 * (z ^ 2 + μ * z + a) - (2 * z + μ) ^ 2) / (2 * (z ^ 2 + μ * z + a) ^ 2) +
          3 / (2 * z ^ 2)) +
        c ^ 2 * z ^ 2 / ((z ^ 2 + μ * z + a) ^ 2 * (z * (z - 1) * (z - a))) = 0 := by
      have hlam : lam = μ - 3 * a - 3 := by rw [hμ]; ring
      have hc2' : c ^ 2 = -((μ + a + 1) * (μ ^ 2 - 4 * a)) / 4 := by
        rw [hc2, hμ]; ring
      clear_value μ
      rw [hc2', hlam]
      simp only [heunCoeffR, heunCoeffP]
      field_simp
      ring
    have E2 : heunCoeffP a (5 / 2) (1 / 2) (1 / 2) z +
        2 * ((2 * z + μ) / (2 * (z ^ 2 + μ * z + a)) - 3 / (2 * z)) + 1 / z -
        (2 * z + μ) / (z ^ 2 + μ * z + a) -
        (3 * z ^ 2 - 2 * (1 + a) * z + a) / (2 * (z * (z - 1) * (z - a))) = 0 := by
      simp only [heunCoeffP]
      field_simp
      ring
    linear_combination E1 + B * E2 + hB2

/-! ### Type I integral equations (§31.10(i)) -/

/-- DLMF 31.10.1–31.10.6: if `w` solves Heun's equation on `V`, the kernel `𝒦(z, t)` solves
`(𝒟_z - 𝒟_t)𝒦 = 0` (31.10.3, Heun's operator 31.10.4), `ρ` is a branch on `V` of the weight
`t^{γ-1}(t-1)^{δ-1}(t-a)^{ε-1}` (31.10.2, given by its logarithmic derivative), and the
contour `C` (a `C¹` path in `V`) is such that the concomitant
`p(t)(∂𝒦/∂t w(t) - 𝒦 dw/dt)`, `p(t) = t(t-1)(t-a)ρ(t)` (31.10.5–31.10.6), takes equal values at
the two ends, then `W(z) = ∫_C 𝒦(z, t) w(t) ρ(t) dt` (31.10.1) is a solution of Heun's
equation.
Stronger than DLMF: Fuchs's relation `α + β + 1 = γ + δ + ε` and the openness of `V` are not
needed. -/
@[dlmf 31.10.E1, dlmf 31.10.E2, dlmf 31.10.E3, dlmf 31.10.E5, dlmf 31.10.E6]
theorem heun_integral_typeI' {U V : Set ℂ} (hU : IsOpen U)
    (hUs : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a)
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
  set g : ℝ → ℂ := fun s => w (C s) * ρ (C s) * deriv C s with hg
  have hfun : (fun z => ∫ s in (0 : ℝ)..1, K z (C s) * w (C s) * ρ (C s) * deriv C s) =
      fun z => ∫ s in (0 : ℝ)..1, K z (C s) * g s := by
    funext z; congr 1; funext s; simp only [hg]; ring
  rw [hfun]
  set K1 : ℂ → ℂ → ℂ := fun z t => deriv (fun z' => K z' t) z with hK1
  set K2 : ℂ → ℂ → ℂ := fun z t => deriv (fun z' => K1 z' t) z with hK2
  have hA1 : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => K1 x.1 x.2) (U ×ˢ V) := fun x hx =>
    Complex.analyticAt_deriv_fst (F := fun x : ℂ × ℂ => K x.1 x.2) (hK x hx)
  have hA2 : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => K2 x.1 x.2) (U ×ˢ V) := fun x hx =>
    Complex.analyticAt_deriv_fst (F := fun x : ℂ × ℂ => K1 x.1 x.2) (hA1 x hx)
  have hslz : ∀ {G : ℂ → ℂ → ℂ}, AnalyticOnNhd ℂ (fun x : ℂ × ℂ => G x.1 x.2) (U ×ˢ V) →
      ∀ z ∈ U, ∀ t ∈ V, HasDerivAt (fun z' => G z' t) (deriv (fun z' => G z' t) z) z :=
    fun {G} hG z hz t ht => (AnalyticAt.comp (g := fun x : ℂ × ℂ => G x.1 x.2)
      (f := fun z' : ℂ => (z', t)) (hG (z, t) ⟨hz, ht⟩)
      (analyticAt_id.prod analyticAt_const)).differentiableAt.hasDerivAt
  have hslt : ∀ z ∈ U, ∀ t ∈ V, AnalyticAt ℂ (K z) t := fun z hz t ht =>
    AnalyticAt.comp (g := fun x : ℂ × ℂ => K x.1 x.2) (f := fun t' : ℂ => (z, t'))
      (hK (z, t) ⟨hz, ht⟩) (analyticAt_const.prod analyticAt_id)
  obtain ⟨MC, hMC⟩ := hC.exists_bound_deriv_Icc_zero_one
  have hCc : ContinuousOn C (Icc 0 1) := hC.continuousOn
  have hwc : ContinuousOn w V := fun t ht => (hw.1 t ht).continuousAt.continuousWithinAt
  have hρc : ContinuousOn ρ V := fun t ht => (hρ t ht).continuousAt.continuousWithinAt
  have hwρC : ContinuousOn (fun s => w (C s) * ρ (C s)) (Icc 0 1) :=
    (hwc.comp hCc hCV).mul (hρc.comp hCc hCV)
  obtain ⟨Mw, hMw⟩ := isCompact_Icc.exists_bound_of_continuousOn hwρC
  have hgm : AEStronglyMeasurable g (volume.restrict (uIoc (0 : ℝ) 1)) :=
    (ContinuousOn.aestronglyMeasurable_uIoc_zero_one hwρC).mul
      (measurable_deriv C).aestronglyMeasurable
  have hgM : ∀ s ∈ Icc (0 : ℝ) 1, ‖g s‖ ≤ Mw * MC := fun s hs => by
    simp only [hg]; rw [norm_mul]
    exact mul_le_mul (hMw s hs) (hMC s hs) (norm_nonneg _) ((norm_nonneg _).trans (hMw s hs))
  have hint : ∀ {G : ℂ → ℂ → ℂ}, ContinuousOn (fun x : ℂ × ℂ => G x.1 x.2) (U ×ˢ V) →
      ∀ z ∈ U, IntervalIntegrable (fun s => G z (C s) * g s) volume 0 1 := by
    intro G hG z hz
    have hc : ContinuousOn (fun s => G z (C s)) (Icc 0 1) :=
      hG.comp (continuousOn_const.prodMk hCc) fun s hs => ⟨hz, hCV s hs⟩
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    refine intervalIntegrable_zero_one_of_bound
      ((ContinuousOn.aestronglyMeasurable_uIoc_zero_one hc).mul hgm) (B := B * (Mw * MC))
      fun s hs => ?_
    rw [norm_mul]
    exact mul_le_mul (hB s hs) (hgM s hs) (norm_nonneg _) ((norm_nonneg _).trans (hB s hs))
  have hW1 : ∀ z ∈ U, HasDerivAt (fun z => ∫ s in (0 : ℝ)..1, K z (C s) * g s)
      (∫ s in (0 : ℝ)..1, K1 z (C s) * g s) z := fun z hz =>
    hasDerivAt_intervalIntegral_mul_comp_path hU hCc hCV hgm hgM hK.continuousOn hA1.continuousOn
      (fun z hz t ht => hslz hK z hz t ht) hz
  have hW2 : ∀ z ∈ U, HasDerivAt (fun z => ∫ s in (0 : ℝ)..1, K1 z (C s) * g s)
      (∫ s in (0 : ℝ)..1, K2 z (C s) * g s) z := fun z hz =>
    hasDerivAt_intervalIntegral_mul_comp_path hU hCc hCV hgm hgM hA1.continuousOn hA2.continuousOn
      (fun z hz t ht => hslz hA1 z hz t ht) hz
  refine ⟨fun z hz => (hW1 z hz).differentiableAt, fun z hz => ?_⟩
  have hev : deriv (fun z => ∫ s in (0 : ℝ)..1, K z (C s) * g s) =ᶠ[𝓝 z]
      fun z => ∫ s in (0 : ℝ)..1, K1 z (C s) * g s :=
    eventually_of_mem (hU.mem_nhds hz) fun y hy => (hW1 y hy).deriv
  refine ((hW2 z hz).congr_of_eventuallyEq hev).congr_deriv ?_
  rw [(hW1 z hz).deriv]
  obtain ⟨hz0, hz1, hza⟩ := hUs z hz
  have hL : ∫ s in (0 : ℝ)..1, heunOperator a α β γ δ ε (K z) (C s) * g s =
      q * ∫ s in (0 : ℝ)..1, K z (C s) * g s :=
    integral_heunOperator_comp_path hVs hw hρ (hslt z hz) hC hCV (hbd z hz)
  -- the key identity `𝒟_z W = q W`
  have key : z * (z - 1) * (z - a) * (∫ s in (0 : ℝ)..1, K2 z (C s) * g s) +
      (γ * (z - 1) * (z - a) + δ * z * (z - a) + ε * z * (z - 1)) *
        (∫ s in (0 : ℝ)..1, K1 z (C s) * g s) + α * β * z * (∫ s in (0 : ℝ)..1, K z (C s) * g s) =
      q * ∫ s in (0 : ℝ)..1, K z (C s) * g s := by
    have i0 := hint hK.continuousOn z hz
    have i1 := hint hA1.continuousOn z hz
    have i2 := hint hA2.continuousOn z hz
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (i2.const_mul _)
        (i1.const_mul _), ← intervalIntegral.integral_add ((i2.const_mul _).add (i1.const_mul _))
        (i0.const_mul _), ← hL]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    have hpde := hKpde z hz (C s) (hCV s hs)
    simp only [heunOperator] at hpde
    simp only [heunOperator]
    linear_combination g s * hpde
  simp only [heunCoeffP, heunCoeffR]
  have h0 : z - 1 ≠ 0 := sub_ne_zero.2 hz1
  have h1 : z - a ≠ 0 := sub_ne_zero.2 hza
  field_simp
  linear_combination key

/-- DLMF 31.10.1–31.10.6: if `w` solves Heun's equation on `V`, the kernel `𝒦(z, t)` solves
`(𝒟_z - 𝒟_t)𝒦 = 0` (31.10.3, Heun's operator 31.10.4), `ρ` is a branch on `V` of the weight
`t^{γ-1}(t-1)^{δ-1}(t-a)^{ε-1}` (31.10.2, given by its logarithmic derivative), and the
contour `C` (a `C¹` path in `V`) is such that the concomitant
`p(t)(∂𝒦/∂t w(t) - 𝒦 dw/dt)`, `p(t) = t(t-1)(t-a)ρ(t)` (31.10.5–31.10.6), takes equal values at
the two ends, then `W(z) = ∫_C 𝒦(z, t) w(t) ρ(t) dt` (31.10.1) is a solution of Heun's
equation. -/
@[dlmf 31.10.E1, dlmf 31.10.E2, dlmf 31.10.E3, dlmf 31.10.E5, dlmf 31.10.E6]
theorem heun_integral_typeI (_hF : α + β + 1 = γ + δ + ε) {U V : Set ℂ} (hU : IsOpen U)
    (_hV : IsOpen V) (hUs : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a)
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
  exact heun_integral_typeI' hU hUs hVs hw hρ hK hKpde hC hCV hbd

/-- DLMF 31.10.7–31.10.8 (**31.10.8 sign corrected**): with
`cos²θ = zt/a`, `sin²θ cos²φ = -(z-a)(t-a)/(a(1-a))`, `sin²θ sin²φ = (z-1)(t-1)/(1-a)`
(31.10.7 squared), a kernel `𝒦(z, t)` with `(𝒟_z - 𝒟_t)𝒦 = 0` satisfies, as a function of
`(θ, φ)`, `sin²θ(𝒦_θθ + ((1-2γ)tan θ + 2(δ+ε-1/2)cot θ)𝒦_θ - 4αβ𝒦) + 𝒦_φφ
+ ((2δ-1)cot φ - (2ε-1)tan φ)𝒦_φ = 0`. Stated for analytic `Z, T` of `(θ, φ)` satisfying the
relations on an open set where the change of variables is valid. -/
@[dlmf 31.10.E7, dlmf 31.10.E8]
theorem heun_kernel_typeI_angles (_hF : α + β + 1 = γ + δ + ε) (_ha0 : a ≠ 0) (_ha1 : a ≠ 1)
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
  exact heun_kernel_typeI_angles' hΩ hZT (fun x hx => ⟨(hrel x hx).1, (hrel x hx).2.1⟩) hreg hK
    hKpde

/-- Chain rule for `t ↦ C · u(cos² t)`: first and second derivatives. -/
private lemma deriv_cos_sq_comp {u : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hu : ContDiffOn ℂ 2 u U)
    (C : ℂ) {t : ℂ} (ht : Complex.cos t ^ 2 ∈ U) :
    deriv (fun t' => C * u (Complex.cos t' ^ 2)) t =
        C * (deriv u (Complex.cos t ^ 2) * (-2 * Complex.cos t * Complex.sin t)) ∧
      deriv (deriv fun t' => C * u (Complex.cos t' ^ 2)) t =
        C * (deriv (deriv u) (Complex.cos t ^ 2) * (-2 * Complex.cos t * Complex.sin t) ^ 2 +
          deriv u (Complex.cos t ^ 2) * (2 * Complex.sin t ^ 2 - 2 * Complex.cos t ^ 2)) := by
  have hd : DifferentiableOn ℂ u U := hu.differentiableOn (by norm_num)
  have hd2 : DifferentiableOn ℂ (deriv u) U :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hU).1 hu).2.2.differentiableOn (by norm_num)
  have hh : ∀ s, HasDerivAt (fun t' => Complex.cos t' ^ 2)
      (-2 * Complex.cos s * Complex.sin s) s := fun s => by
    convert (Complex.hasDerivAt_cos s).pow 2 using 1
    simp
  have hW : IsOpen {s : ℂ | Complex.cos s ^ 2 ∈ U} := hU.preimage (by fun_prop)
  have hD : ∀ s ∈ {s : ℂ | Complex.cos s ^ 2 ∈ U}, HasDerivAt (fun t' => C * u (Complex.cos t' ^ 2))
      (C * (deriv u (Complex.cos s ^ 2) * (-2 * Complex.cos s * Complex.sin s))) s :=
    fun s hs => ((hd.differentiableAt (hU.mem_nhds hs)).hasDerivAt.comp s (hh s)).const_mul C
  refine ⟨(hD t ht).deriv, ?_⟩
  have ev : deriv (fun t' => C * u (Complex.cos t' ^ 2)) =ᶠ[𝓝 t]
      fun s => C * (deriv u (Complex.cos s ^ 2) * (-2 * Complex.cos s * Complex.sin s)) :=
    eventually_of_mem (hW.mem_nhds ht) fun s hs => (hD s hs).deriv
  rw [ev.deriv_eq]
  have hc := ((Complex.hasDerivAt_cos t).const_mul (-2)).mul (Complex.hasDerivAt_sin t)
  have := (((hd2.differentiableAt (hU.mem_nhds ht)).hasDerivAt.comp t (hh t)).mul hc).const_mul C
  refine this.deriv.trans ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  ring

/-- The normalized Riemann equation with `a₁ = 0`, cleared of denominators. -/
private lemma riemannNormalOperator_zero_cleared {a₂ b₁ b₂ c₁ c₂ x : ℂ} {u : ℂ → ℂ} (hx0 : x ≠ 0)
    (hx1 : 1 - x ≠ 0)
    (h : DLMF.Hypergeometric.riemannNormalOperator 0 a₂ b₁ b₂ c₁ c₂ u x = 0) :
    x * (1 - x) ^ 2 * deriv (deriv u) x +
      ((1 - a₂) * (1 - x) ^ 2 - (1 - b₁ - b₂) * x * (1 - x)) * deriv u x +
      (b₁ * b₂ - c₁ * c₂ * (1 - x)) * u x = 0 := by
  have hx1' : x - 1 ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 hx1
  calc _ = x * (1 - x) ^ 2 * DLMF.Hypergeometric.riemannNormalOperator 0 a₂ b₁ b₂ c₁ c₂ u x := by
          simp only [DLMF.Hypergeometric.riemannNormalOperator, iteratedDeriv_succ,
            iteratedDeriv_zero]
          field_simp
          ring
    _ = 0 := by rw [h, mul_zero]

/-- The normalized Riemann equation with `a₁ = b₁ = 0`, cleared of denominators. -/
private lemma riemannNormalOperator_zero_zero_cleared {a₂ b₂ c₁ c₂ x : ℂ} {u : ℂ → ℂ} (hx0 : x ≠ 0)
    (hx1 : 1 - x ≠ 0)
    (h : DLMF.Hypergeometric.riemannNormalOperator 0 a₂ 0 b₂ c₁ c₂ u x = 0) :
    x * (1 - x) * deriv (deriv u) x + ((1 - a₂) * (1 - x) - (1 - b₂) * x) * deriv u x -
      c₁ * c₂ * u x = 0 := by
  have hx1' : x - 1 ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 hx1
  calc _ = x * (1 - x) * DLMF.Hypergeometric.riemannNormalOperator 0 a₂ 0 b₂ c₁ c₂ u x := by
          simp only [DLMF.Hypergeometric.riemannNormalOperator, iteratedDeriv_succ,
            iteratedDeriv_zero]
          field_simp
          ring
    _ = 0 := by rw [h, mul_zero]

/-- DLMF 31.10.9: the separable solutions of the (corrected) kernel equation 31.10.8:
`𝒦(θ, φ) = f(cos²θ) g(cos²φ)` with `f ∈ P{0, 1, ∞; 0, 1/2-δ-σ, α; 1-γ, 1/2-ε+σ, β; ·}` and
`g ∈ P{0, 1, ∞; 0, 0, -1/2+δ+σ; 1-ε, 1-δ, -1/2+ε-σ; ·}` (Riemann's equation,
`riemannNormalOperator`), `σ` a separation constant. -/
@[dlmf 31.10.E9, dlmf 31.10.E8]
theorem heun_kernel_typeI_separable (σ : ℂ) {f g : ℂ → ℂ}
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
  intro 𝒦
  obtain ⟨hs, hc, hs', hc'⟩ := hreg
  have eθ : (fun θ' => 𝒦 θ' φ) = fun θ' => g (Complex.cos φ ^ 2) * f (Complex.cos θ' ^ 2) :=
    funext fun _ => mul_comm _ _
  have eφ : 𝒦 θ = fun φ' => f (Complex.cos θ ^ 2) * g (Complex.cos φ' ^ 2) := rfl
  obtain ⟨d1, d2⟩ := deriv_cos_sq_comp hUf hf.1 (g (Complex.cos φ ^ 2)) hθ
  obtain ⟨e1, e2⟩ := deriv_cos_sq_comp hUg hg.1 (f (Complex.cos θ ^ 2)) hφ
  have hK : 𝒦 θ φ = f (Complex.cos θ ^ 2) * g (Complex.cos φ ^ 2) := rfl
  rw [eθ, eφ, d1, d2, e1, e2]
  beta_reduce
  have hsc := Complex.sin_sq_add_cos_sq θ
  have hsc' := Complex.sin_sq_add_cos_sq φ
  have hx1 : 1 - Complex.cos θ ^ 2 ≠ 0 := by
    rw [← hsc]; ring_nf; exact pow_ne_zero _ hs
  have hy1 : 1 - Complex.cos φ ^ 2 ≠ 0 := by
    rw [← hsc']; ring_nf; exact pow_ne_zero _ hs'
  have Rf := riemannNormalOperator_zero_cleared (pow_ne_zero 2 hc) hx1 (hf.2 _ hθ)
  have Rg := riemannNormalOperator_zero_zero_cleared (pow_ne_zero 2 hc') hy1 (hg.2 _ hφ)
  have ht : Complex.tan θ * (-2 * Complex.cos θ * Complex.sin θ) = -2 * Complex.sin θ ^ 2 := by
    rw [Complex.tan_eq_sin_div_cos]; field_simp
  have hct : Complex.cot θ * (-2 * Complex.cos θ * Complex.sin θ) = -2 * Complex.cos θ ^ 2 := by
    rw [Complex.cot_eq_cos_div_sin]; field_simp
  have ht' : Complex.tan φ * (-2 * Complex.cos φ * Complex.sin φ) = -2 * Complex.sin φ ^ 2 := by
    rw [Complex.tan_eq_sin_div_cos]; field_simp
  have hct' : Complex.cot φ * (-2 * Complex.cos φ * Complex.sin φ) = -2 * Complex.cos φ ^ 2 := by
    rw [Complex.cot_eq_cos_div_sin]; field_simp
  set F0 := f (Complex.cos θ ^ 2)
  set F1 := deriv f (Complex.cos θ ^ 2)
  set F2 := deriv (deriv f) (Complex.cos θ ^ 2)
  set G0 := g (Complex.cos φ ^ 2)
  set G1 := deriv g (Complex.cos φ ^ 2)
  set G2 := deriv (deriv g) (Complex.cos φ ^ 2)
  set c := Complex.cos θ
  set s := Complex.sin θ
  set c' := Complex.cos φ
  set s' := Complex.sin φ
  linear_combination (s ^ 2 * G0 * F1 * (1 - 2 * γ)) * ht +
    (s ^ 2 * G0 * F1 * (2 * (δ + ε - 1 / 2))) * hct + (F0 * G1 * (2 * δ - 1)) * hct' -
    (F0 * G1 * (2 * ε - 1)) * ht' + 4 * G0 * Rf + 4 * F0 * Rg +
    (4 * G0 * (-F0 * α * β - F1 * c ^ 2 * δ - F1 * c ^ 2 * ε - F1 * c ^ 2 * γ + F1 * γ * s ^ 2 +
      F1 * γ - F2 * c ^ 4 + F2 * c ^ 2 * s ^ 2 + F2 * c ^ 2)) * hsc +
    (4 * F0 * (G1 * ε + G2 * c' ^ 2)) * hsc'

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
theorem heun_integral_typeII (_hF : α + β + 1 = γ + δ + ε) {U V : Set ℂ} (hU : IsOpen U)
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
  exact heun_integral_typeII' hU hV hUs hVs hw hρ hK hKpde hC₁ hC₂ hC₁V hC₂V hbd₂ hbd₁

/-- Derivatives of `σ ↦ (c(σ - b))^{1/2}`: the first derivative is `f^{1/2}/(2(σ - b))`, and the
derivative of that at `s` is `-f(s)^{1/2}/(4(s - b)²)`. -/
private lemma hasDerivAt_sqrt_affine {f : ℂ → ℂ} {c b s : ℂ} (hf : ∀ σ, f σ = c * (σ - b))
    (hs : f s ∈ slitPlane) :
    (∀ᶠ σ in 𝓝 s, HasDerivAt (fun σ => f σ ^ (1 / 2 : ℂ)) (f σ ^ (1 / 2 : ℂ) / (2 * (σ - b))) σ) ∧
      HasDerivAt (fun σ => f σ ^ (1 / 2 : ℂ) / (2 * (σ - b)))
        (-(f s ^ (1 / 2 : ℂ)) / (4 * (s - b) ^ 2)) s := by
  have hfe : f = fun σ => c * (σ - b) := funext hf
  have hfd : ∀ σ, HasDerivAt f c σ := fun σ => by
    rw [hfe]; simpa using ((hasDerivAt_id σ).sub_const b).const_mul c
  have hcont : Continuous f := by rw [hfe]; fun_prop
  have hev : ∀ᶠ σ in 𝓝 s, f σ ∈ slitPlane :=
    hcont.continuousAt.eventually_mem (isOpen_slitPlane.mem_nhds hs)
  have hd : ∀ σ, f σ ∈ slitPlane →
      HasDerivAt (fun σ => f σ ^ (1 / 2 : ℂ)) (f σ ^ (1 / 2 : ℂ) / (2 * (σ - b))) σ := by
    intro σ hσ
    have h0 : f σ ≠ 0 := slitPlane_ne_zero hσ
    have hc0 : c ≠ 0 := fun h => h0 (by rw [hf, h, zero_mul])
    have hb0 : σ - b ≠ 0 := fun h => h0 (by rw [hf, h, mul_zero])
    refine ((hfd σ).cpow_const hσ).congr_deriv ?_
    rw [cpow_sub _ _ h0, cpow_one]
    rw [hf] at h0 ⊢
    field_simp
  refine ⟨hev.mono hd, ?_⟩
  have h0 : f s ≠ 0 := slitPlane_ne_zero hs
  have hb0 : s - b ≠ 0 := fun h => h0 (by rw [hf, h, mul_zero])
  have h2 : HasDerivAt (fun σ : ℂ => 2 * (σ - b)) 2 s := by
    simpa using ((hasDerivAt_id s).sub_const b).const_mul (2 : ℂ)
  refine ((hd s hs).div h2 (mul_ne_zero two_ne_zero hb0)).congr_deriv ?_
  field_simp
  ring

/-- Heun's operator along a curve `x ↦ (U, V, I W)` whose coordinates have the derivatives of
`(c(x - b))^{1/2}` with `b = 0, 1, a`. -/
private lemma heunOperator_sqrt_curve {a α β γ δ ε : ℂ} {f : ℂ → ℂ}
    {x U V W H11 H22 H33 H12 H13 H23 g1 g2 g3 : ℂ}
    (hx0 : x ≠ 0) (hx1 : x - 1 ≠ 0) (hxa : x - a ≠ 0)
    (h1 : deriv f x = U / (2 * (x - 0)) * g1 + V / (2 * (x - 1)) * g2 +
      I * (W / (2 * (x - a))) * g3)
    (h2 : deriv (deriv f) x = (U / (2 * (x - 0))) ^ 2 * H11 + (V / (2 * (x - 1))) ^ 2 * H22 +
      (I * (W / (2 * (x - a)))) ^ 2 * H33 + 2 * (U / (2 * (x - 0))) * (V / (2 * (x - 1))) * H12 +
      2 * (U / (2 * (x - 0))) * (I * (W / (2 * (x - a)))) * H13 +
      2 * (V / (2 * (x - 1))) * (I * (W / (2 * (x - a)))) * H23 +
      -U / (4 * (x - 0) ^ 2) * g1 + -V / (4 * (x - 1) ^ 2) * g2 +
      I * (-W / (4 * (x - a) ^ 2)) * g3) :
    heunOperator a α β γ δ ε f x =
      (x - 1) * (x - a) / (4 * x) * U ^ 2 * H11 + x * (x - a) / (4 * (x - 1)) * V ^ 2 * H22 +
        x * (x - 1) / (4 * (x - a)) * (I * W) ^ 2 * H33 + (x - a) / 2 * U * V * H12 +
        (x - 1) / 2 * U * (I * W) * H13 + x / 2 * V * (I * W) * H23 +
        (U * (x - 1) * (x - a) * (2 * γ - 1) / (4 * x) + U * (δ * (x - a) + ε * (x - 1)) / 2) * g1 +
        (V * x * (x - a) * (2 * δ - 1) / (4 * (x - 1)) + V * (γ * (x - a) + ε * x) / 2) * g2 +
        ((I * W) * x * (x - 1) * (2 * ε - 1) / (4 * (x - a)) +
          (I * W) * (γ * (x - 1) + δ * x) / 2) * g3 + α * β * x * f x := by
  rw [heunOperator, h1, h2, sub_zero]
  field_simp
  ring

/-- DLMF 31.10.17–31.10.18 (**31.10.17 corrected**: `u = (stz/a)^{1/2}`): with
`u = (stz/a)^{1/2}`, `v = ((s-1)(t-1)(z-1)/(1-a))^{1/2}`, `w = i((s-a)(t-a)(z-a)/(a(1-a)))^{1/2}`
(principal roots), a function `𝒦(u, v, w)` with
`𝒦_uu + 𝒦_vv + 𝒦_ww + ((2γ-1)/u)𝒦_u + ((2δ-1)/v)𝒦_v + ((2ε-1)/w)𝒦_w = 0` (31.10.18) gives a
kernel `𝒦(u, v, w)` satisfying 31.10.14, at points where the roots are analytic and nonzero.
Stronger than DLMF: the hypotheses `α + β + 1 = γ + δ + ε`, `a ≠ 0`, `a ≠ 1` and the
openness of `Ω` are not needed. -/
@[dlmf 31.10.E17, dlmf 31.10.E18, dlmf 31.10.E14]
theorem heun_kernel_typeII_uvw'
    {Ω : Set (ℂ × ℂ × ℂ)} {𝒦 : ℂ → ℂ → ℂ → ℂ}
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
  intro K
  obtain ⟨hp1, hp2, hp3⟩ := hpt
  have hFp := (h𝒦 _ hΩpt).contDiffAt (n := 2)
  -- the `s`-curve
  have hUs := hasDerivAt_sqrt_affine (f := fun σ => σ * t * z / a) (c := t * z / a) (b := 0)
    (s := s) (fun σ => by ring) hp1
  have hVs := hasDerivAt_sqrt_affine (f := fun σ => (σ - 1) * (t - 1) * (z - 1) / (1 - a))
    (c := (t - 1) * (z - 1) / (1 - a)) (b := 1) (s := s) (fun σ => by ring) hp2
  have hWs := hasDerivAt_sqrt_affine (f := fun σ => (σ - a) * (t - a) * (z - a) / (a * (1 - a)))
    (c := (t - a) * (z - a) / (a * (1 - a))) (b := a) (s := s) (fun σ => by ring) hp3
  have Ds := Complex.deriv_comp_three (𝒦 := 𝒦) hFp hUs.1 hVs.1
    (hWs.1.mono fun σ h => h.const_mul I) hUs.2 hVs.2 (hWs.2.const_mul I)
  -- the `t`-curve
  have hUt := hasDerivAt_sqrt_affine (f := fun σ => s * σ * z / a) (c := s * z / a) (b := 0)
    (s := t) (fun σ => by ring) hp1
  have hVt := hasDerivAt_sqrt_affine (f := fun σ => (s - 1) * (σ - 1) * (z - 1) / (1 - a))
    (c := (s - 1) * (z - 1) / (1 - a)) (b := 1) (s := t) (fun σ => by ring) hp2
  have hWt := hasDerivAt_sqrt_affine (f := fun σ => (s - a) * (σ - a) * (z - a) / (a * (1 - a)))
    (c := (s - a) * (z - a) / (a * (1 - a))) (b := a) (s := t) (fun σ => by ring) hp3
  have Dt := Complex.deriv_comp_three (𝒦 := 𝒦) hFp hUt.1 hVt.1
    (hWt.1.mono fun σ h => h.const_mul I) hUt.2 hVt.2 (hWt.2.const_mul I)
  -- the `z`-curve
  have hUz := hasDerivAt_sqrt_affine (f := fun σ => s * t * σ / a) (c := s * t / a) (b := 0)
    (s := z) (fun σ => by ring) hp1
  have hVz := hasDerivAt_sqrt_affine (f := fun σ => (s - 1) * (t - 1) * (σ - 1) / (1 - a))
    (c := (s - 1) * (t - 1) / (1 - a)) (b := 1) (s := z) (fun σ => by ring) hp2
  have hWz := hasDerivAt_sqrt_affine (f := fun σ => (s - a) * (t - a) * (σ - a) / (a * (1 - a)))
    (c := (s - a) * (t - a) / (a * (1 - a))) (b := a) (s := z) (fun σ => by ring) hp3
  have Dz := Complex.deriv_comp_three (𝒦 := 𝒦) hFp hUz.1 hVz.1
    (hWz.1.mono fun σ h => h.const_mul I) hUz.2 hVz.2 (hWz.2.const_mul I)
  have Dc := Complex.deriv_coord_three hFp
  have hP := hpde _ hΩpt
  beta_reduce at Ds Dt Dz Dc hP
  simp only [K]
  dsimp only at hP
  rw [Dc.1, Dc.2.1, Dc.2.2.1, Dc.2.2.2.1, Dc.2.2.2.2.1, Dc.2.2.2.2.2] at hP
  have hsq : ∀ x : ℂ, (x ^ (1 / 2 : ℂ)) ^ 2 = x := fun x => by
    rw [one_div]; exact cpow_ofNat_inv_pow x 2
  have hU2 := hsq (s * t * z / a)
  have hV2 := hsq ((s - 1) * (t - 1) * (z - 1) / (1 - a))
  have hW2 : (I * ((s - a) * (t - a) * (z - a) / (a * (1 - a))) ^ (1 / 2 : ℂ)) ^ 2 =
      -((s - a) * (t - a) * (z - a) / (a * (1 - a))) := by
    rw [mul_pow, I_sq, hsq]; ring
  have h1 := slitPlane_ne_zero hp1
  have h2 := slitPlane_ne_zero hp2
  have h3 := slitPlane_ne_zero hp3
  simp only [ne_eq, div_eq_zero_iff, mul_eq_zero, not_or] at h1 h2 h3
  obtain ⟨⟨⟨hs0, ht0⟩, hz0⟩, ha0⟩ := h1
  obtain ⟨⟨⟨hs1, ht1⟩, hz1⟩, ha1⟩ := h2
  obtain ⟨⟨⟨hsa, hta⟩, hza⟩, -, -⟩ := h3
  rw [heunOperator_sqrt_curve hs0 hs1 hsa Ds.1 Ds.2, heunOperator_sqrt_curve ht0 ht1 hta Dt.1 Dt.2,
    heunOperator_sqrt_curve hz0 hz1 hza Dz.1 Dz.2]
  set F := fun x : ℂ × ℂ × ℂ => 𝒦 x.1 x.2.1 x.2.2 with hFdef
  set p : ℂ × ℂ × ℂ := ((s * t * z / a) ^ (1 / 2 : ℂ),
    ((s - 1) * (t - 1) * (z - 1) / (1 - a)) ^ (1 / 2 : ℂ),
    I * ((s - a) * (t - a) * (z - a) / (a * (1 - a))) ^ (1 / 2 : ℂ)) with hpdef
  set H11 := fderiv ℂ (fderiv ℂ F) p (1, 0, 0) (1, 0, 0)
  set H22 := fderiv ℂ (fderiv ℂ F) p (0, 1, 0) (0, 1, 0)
  set H33 := fderiv ℂ (fderiv ℂ F) p (0, 0, 1) (0, 0, 1)
  set g1 := fderiv ℂ F p (1, 0, 0)
  set g2 := fderiv ℂ F p (0, 1, 0)
  set g3 := fderiv ℂ F p (0, 0, 1)
  set U := (s * t * z / a) ^ (1 / 2 : ℂ)
  set V := ((s - 1) * (t - 1) * (z - 1) / (1 - a)) ^ (1 / 2 : ℂ)
  set W := ((s - a) * (t - a) * (z - a) / (a * (1 - a))) ^ (1 / 2 : ℂ)
  have hU0 : U ≠ 0 := fun h => by
    rw [h, zero_pow two_ne_zero] at hU2
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hs0 ht0) hz0) ha0 hU2.symm
  have hV0 : V ≠ 0 := fun h => by
    rw [h, zero_pow two_ne_zero] at hV2
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hs1 ht1) hz1) ha1 hV2.symm
  have hW0 : W ≠ 0 := fun h => by
    rw [h, mul_zero, zero_pow two_ne_zero] at hW2
    have : (s - a) * (t - a) * (z - a) / (a * (1 - a)) = 0 := by linear_combination hW2
    simp only [div_eq_zero_iff, mul_eq_zero] at this
    rcases this with ((h | h) | h) | (h | h)
    · exact hsa h
    · exact hta h
    · exact hza h
    · exact ha0 h
    · exact ha1 h
  have hI : I ≠ 0 := I_ne_zero
  have hIW : I * W ≠ 0 := mul_ne_zero hI hW0
  set P := (s - t) * (t - z) * (z - s) with hPdef
  have e11 : (t - z) * ((s - 1) * (s - a) / (4 * s) * U ^ 2) +
      (z - s) * ((t - 1) * (t - a) / (4 * t) * U ^ 2) +
      (s - t) * ((z - 1) * (z - a) / (4 * z) * U ^ 2) = -P / 4 := by
    rw [hU2, hPdef]; field_simp; ring
  have e22 : (t - z) * (s * (s - a) / (4 * (s - 1)) * V ^ 2) +
      (z - s) * (t * (t - a) / (4 * (t - 1)) * V ^ 2) +
      (s - t) * (z * (z - a) / (4 * (z - 1)) * V ^ 2) = -P / 4 := by
    rw [hV2, hPdef]; field_simp; ring
  have e33 : (t - z) * (s * (s - 1) / (4 * (s - a)) * (I * W) ^ 2) +
      (z - s) * (t * (t - 1) / (4 * (t - a)) * (I * W) ^ 2) +
      (s - t) * (z * (z - 1) / (4 * (z - a)) * (I * W) ^ 2) = -P / 4 := by
    rw [hW2, hPdef]; field_simp; ring
  have eg1 : (t - z) * (U * (s - 1) * (s - a) * (2 * γ - 1) / (4 * s) +
        U * (δ * (s - a) + ε * (s - 1)) / 2) +
      (z - s) * (U * (t - 1) * (t - a) * (2 * γ - 1) / (4 * t) +
        U * (δ * (t - a) + ε * (t - 1)) / 2) +
      (s - t) * (U * (z - 1) * (z - a) * (2 * γ - 1) / (4 * z) +
        U * (δ * (z - a) + ε * (z - 1)) / 2) = -P / 4 * ((2 * γ - 1) / U) := by
    rw [show (2 * γ - 1) / U = (2 * γ - 1) * U / U ^ 2 by field_simp, hU2, hPdef]
    field_simp; ring
  have eg2 : (t - z) * (V * s * (s - a) * (2 * δ - 1) / (4 * (s - 1)) +
        V * (γ * (s - a) + ε * s) / 2) +
      (z - s) * (V * t * (t - a) * (2 * δ - 1) / (4 * (t - 1)) +
        V * (γ * (t - a) + ε * t) / 2) +
      (s - t) * (V * z * (z - a) * (2 * δ - 1) / (4 * (z - 1)) +
        V * (γ * (z - a) + ε * z) / 2) = -P / 4 * ((2 * δ - 1) / V) := by
    rw [show (2 * δ - 1) / V = (2 * δ - 1) * V / V ^ 2 by field_simp, hV2, hPdef]
    field_simp; ring
  have eg3 : (t - z) * ((I * W) * s * (s - 1) * (2 * ε - 1) / (4 * (s - a)) +
        (I * W) * (γ * (s - 1) + δ * s) / 2) +
      (z - s) * ((I * W) * t * (t - 1) * (2 * ε - 1) / (4 * (t - a)) +
        (I * W) * (γ * (t - 1) + δ * t) / 2) +
      (s - t) * ((I * W) * z * (z - 1) * (2 * ε - 1) / (4 * (z - a)) +
        (I * W) * (γ * (z - 1) + δ * z) / 2) = -P / 4 * ((2 * ε - 1) / (I * W)) := by
    rw [show (2 * ε - 1) / (I * W) = (2 * ε - 1) * (I * W) / (I * W) ^ 2 by field_simp, hW2,
      hPdef]
    field_simp; ring
  linear_combination (-P / 4) * hP + H11 * e11 + H22 * e22 + H33 * e33 + g1 * eg1 +
    g2 * eg2 + g3 * eg3

/-- DLMF 31.10.17–31.10.18 (**31.10.17 corrected**: `u = (stz/a)^{1/2}`): with
`u = (stz/a)^{1/2}`, `v = ((s-1)(t-1)(z-1)/(1-a))^{1/2}`, `w = i((s-a)(t-a)(z-a)/(a(1-a)))^{1/2}`
(principal roots), a function `𝒦(u, v, w)` with
`𝒦_uu + 𝒦_vv + 𝒦_ww + ((2γ-1)/u)𝒦_u + ((2δ-1)/v)𝒦_v + ((2ε-1)/w)𝒦_w = 0` (31.10.18) gives a
kernel `𝒦(u, v, w)` satisfying 31.10.14, at points where the roots are analytic and nonzero. -/
@[dlmf 31.10.E17, dlmf 31.10.E18, dlmf 31.10.E14]
theorem heun_kernel_typeII_uvw (_hF : α + β + 1 = γ + δ + ε) (_ha0 : a ≠ 0) (_ha1 : a ≠ 1)
    {Ω : Set (ℂ × ℂ × ℂ)} (_hΩ : IsOpen Ω) {𝒦 : ℂ → ℂ → ℂ → ℂ}
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
  exact heun_kernel_typeII_uvw' h𝒦 hpde hpt hΩpt

/-- A Bessel factor: if `𝒞` solves Bessel's equation of order `ν` near `xk`, then
`F(y) = A y^ν 𝒞(yk)` satisfies `F'' + ((1-2ν)/x) F' = -k² F` at `x`. -/
private lemma deriv_bessel_factor {ν k x A : ℂ} {C : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hC : IsLinearODE2On (fun y => 1 / y) (fun y => 1 - ν ^ 2 / y ^ 2) C S)
    (hx : x ∈ slitPlane) (hxS : x * k ∈ S) (hk : k ≠ 0) :
    deriv (deriv fun y => A * (y ^ ν * C (y * k))) x +
        (1 - 2 * ν) / x * deriv (fun y => A * (y ^ ν * C (y * k))) x =
      -k ^ 2 * (A * (x ^ ν * C (x * k))) := by
  set W := {y : ℂ | y ∈ slitPlane ∧ y * k ∈ S}
  have hW : IsOpen W :=
    isOpen_slitPlane.inter (hS.preimage (continuous_id.mul continuous_const))
  have hxW : x ∈ W := ⟨hx, hxS⟩
  have hlin : ∀ y, HasDerivAt (fun y => y * k) k y := fun y => by
    simpa using (hasDerivAt_id' y).mul_const k
  have hD : ∀ y ∈ W, HasDerivAt (fun y => A * (y ^ ν * C (y * k)))
      (A * (ν * y ^ (ν - 1) * C (y * k) + y ^ ν * (deriv C (y * k) * k))) y := fun y hy => by
    have h1 := (hasDerivAt_id' y).cpow_const (c := ν) hy.1
    have h2 := (hC.differentiableAt _ hy.2).hasDerivAt.comp y (hlin y)
    have h3 : HasDerivAt (fun y => A * (y ^ ν * C (y * k))) _ y := (h1.mul h2).const_mul A
    convert h3 using 1
    simp only [Function.comp_apply, mul_one]
  have ev : deriv (fun y => A * (y ^ ν * C (y * k))) =ᶠ[𝓝 x]
      fun y => A * (ν * y ^ (ν - 1) * C (y * k) + y ^ ν * (deriv C (y * k) * k)) :=
    eventually_of_mem (hW.mem_nhds hxW) fun y hy => (hD y hy).deriv
  rw [ev.deriv_eq, (hD x hxW).deriv]
  have h1 := (hasDerivAt_id' x).cpow_const (c := ν - 1) hx
  have h0 := (hasDerivAt_id' x).cpow_const (c := ν) hx
  have h2 := (hC.differentiableAt _ hxS).hasDerivAt.comp x (hlin x)
  have h3 := (hC.hasDerivAt_deriv _ hxS).comp x (hlin x)
  have hd : HasDerivAt
      (fun y => A * (ν * y ^ (ν - 1) * C (y * k) + y ^ ν * (deriv C (y * k) * k))) _ x :=
    (((h1.const_mul ν).mul h2).add (h0.mul (h3.mul_const k))).const_mul A
  rw [hd.deriv]
  have hx0 : x ≠ 0 := slitPlane_ne_zero hx
  have e1 : x ^ (ν - 1) = x ^ ν / x := by rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
  have e2 : x ^ (ν - 1 - 1) = x ^ ν / x ^ 2 := by
    rw [Complex.cpow_sub _ _ hx0, e1, Complex.cpow_one]; ring
  simp only [Function.comp_apply]
  rw [e2, e1]
  field_simp
  ring

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
  intro 𝒦
  obtain ⟨hσ₁, hσ₂, hσ₃⟩ := hσ
  set k₁ := σ₁ ^ (1 / 2 : ℂ) with hk₁
  set k₂ := σ₂ ^ (1 / 2 : ℂ) with hk₂
  set k₃ := (σ₁ + σ₂) ^ (1 / 2 : ℂ) with hk₃
  have sq : ∀ σ : ℂ, (σ ^ (1 / 2 : ℂ)) ^ 2 = σ := fun σ => by
    rw [one_div]; exact Complex.cpow_ofNat_inv_pow σ 2
  have nz : ∀ σ : ℂ, σ ≠ 0 → σ ^ (1 / 2 : ℂ) ≠ 0 := fun σ hσ h => by
    rw [Complex.cpow_eq_zero_iff] at h; exact hσ h.1
  have eU : (fun u' => 𝒦 u' v w) = fun y => (v ^ (1 - δ) * w ^ (1 - ε) * C₂ (v * k₂) *
      C₃ (I * w * k₃)) * (y ^ (1 - γ) * C₁ (y * k₁)) := funext fun y => by ring
  have eV : (fun v' => 𝒦 u v' w) = fun y => (u ^ (1 - γ) * w ^ (1 - ε) * C₁ (u * k₁) *
      C₃ (I * w * k₃)) * (y ^ (1 - δ) * C₂ (y * k₂)) := funext fun y => by ring
  have eW : 𝒦 u v = fun y => (u ^ (1 - γ) * v ^ (1 - δ) * C₁ (u * k₁) * C₂ (v * k₂)) *
      (y ^ (1 - ε) * C₃ (y * (I * k₃))) := funext fun y => by
    rw [show y * (I * k₃) = I * y * k₃ by ring]; ring
  have E1 := deriv_bessel_factor (A := v ^ (1 - δ) * w ^ (1 - ε) * C₂ (v * k₂) *
      C₃ (I * w * k₃)) hS.1 h₁ hu.1 hu.2 (nz _ hσ₁)
  have E2 := deriv_bessel_factor (A := u ^ (1 - γ) * w ^ (1 - ε) * C₁ (u * k₁) *
      C₃ (I * w * k₃)) hS.2.1 h₂ hv.1 hv.2 (nz _ hσ₂)
  have E3 := deriv_bessel_factor (A := u ^ (1 - γ) * v ^ (1 - δ) * C₁ (u * k₁) * C₂ (v * k₂))
    (k := I * k₃) hS.2.2 h₃ hw.1 (by rw [show w * (I * k₃) = I * w * k₃ by ring]; exact hw.2)
    (mul_ne_zero I_ne_zero (nz _ hσ₃))
  rw [show w * (I * k₃) = I * w * k₃ by ring] at E3
  rw [eU, eV, eW]
  have s1 := sq σ₁
  have s2 := sq σ₂
  have s3 := sq (σ₁ + σ₂)
  rw [← hk₁] at s1
  rw [← hk₂] at s2
  rw [← hk₃] at s3
  have hI : I ^ 2 = -1 := I_sq
  set F := u ^ (1 - γ) * v ^ (1 - δ) * w ^ (1 - ε) * C₁ (u * k₁) * C₂ (v * k₂) *
    C₃ (I * w * k₃)
  linear_combination E1 + E2 + E3 - F * s1 - F * s2 - F * I ^ 2 * s3 - F * (σ₁ + σ₂) * hI

/-- DLMF 31.10.20–31.10.21: in spherical coordinates `u = r cos θ`, `v = r sin θ sin φ`,
`w = r sin θ cos φ`, a solution of 31.10.18 satisfies
`𝒦_rr + ((2(γ+δ+ε)-1)/r)𝒦_r + 𝒦_θθ/r² + ((2(δ+ε)-1)cot θ - (2γ-1)tan θ)𝒦_θ/r²
+ 𝒦_φφ/(r² sin²θ) + ((2δ-1)cot φ - (2ε-1)tan φ)𝒦_φ/(r² sin²θ) = 0`.
Stronger than DLMF: the openness of `Ω` is not needed. -/
@[dlmf 31.10.E20, dlmf 31.10.E21]
theorem heun_kernel_typeII_spherical' {Ω : Set (ℂ × ℂ × ℂ)}
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
  intro L
  obtain ⟨hr, hsθ, hcθ, hsφ, hcφ⟩ := hreg
  have hFp := (h𝒦 _ hpt.self_of_nhds).contDiffAt (n := 2)
  have Dr := Complex.deriv_comp_three (𝒦 := 𝒦) (X := fun ρ => ρ * Complex.cos θ)
    (Y := fun ρ => ρ * Complex.sin θ * Complex.sin φ)
    (Z := fun ρ => ρ * Complex.sin θ * Complex.cos φ) (X' := fun _ => Complex.cos θ)
    (Y' := fun _ => Complex.sin θ * Complex.sin φ) (Z' := fun _ => Complex.sin θ * Complex.cos φ)
    (s := r) hFp (Eventually.of_forall fun ρ => hasDerivAt_mul_const _)
    (Eventually.of_forall fun ρ => (hasDerivAt_mul_const _).mul_const _)
    (Eventually.of_forall fun ρ => (hasDerivAt_mul_const _).mul_const _)
    (hasDerivAt_const r _) (hasDerivAt_const r _) (hasDerivAt_const r _)
  have Dθ := Complex.deriv_comp_three (𝒦 := 𝒦) (X := fun ϑ => r * Complex.cos ϑ)
    (Y := fun ϑ => r * Complex.sin ϑ * Complex.sin φ)
    (Z := fun ϑ => r * Complex.sin ϑ * Complex.cos φ) (s := θ) hFp
    (Eventually.of_forall fun ϑ => (Complex.hasDerivAt_cos ϑ).const_mul r)
    (Eventually.of_forall fun ϑ => ((Complex.hasDerivAt_sin ϑ).const_mul r).mul_const _)
    (Eventually.of_forall fun ϑ => ((Complex.hasDerivAt_sin ϑ).const_mul r).mul_const _)
    ((Complex.hasDerivAt_sin θ).neg.const_mul r)
    (((Complex.hasDerivAt_cos θ).const_mul r).mul_const _)
    (((Complex.hasDerivAt_cos θ).const_mul r).mul_const _)
  have Dφ := Complex.deriv_comp_three (𝒦 := 𝒦) (X := fun _ => r * Complex.cos θ)
    (Y := fun ϕ => r * Complex.sin θ * Complex.sin ϕ)
    (Z := fun ϕ => r * Complex.sin θ * Complex.cos ϕ) (s := φ) hFp
    (Eventually.of_forall fun ϕ => hasDerivAt_const ϕ _)
    (Eventually.of_forall fun ϕ => (Complex.hasDerivAt_sin ϕ).const_mul _)
    (Eventually.of_forall fun ϕ => (Complex.hasDerivAt_cos ϕ).const_mul _)
    (hasDerivAt_const φ (0 : ℂ)) ((Complex.hasDerivAt_cos φ).const_mul _)
    ((Complex.hasDerivAt_sin φ).neg.const_mul _)
  have Dc := Complex.deriv_coord_three hFp
  have hP := hpde _ hpt.self_of_nhds
  beta_reduce at Dr Dθ Dφ Dc hP
  dsimp only at hP
  rw [Dc.1, Dc.2.1, Dc.2.2.1, Dc.2.2.2.1, Dc.2.2.2.2.1, Dc.2.2.2.2.2] at hP
  simp only [L]
  rw [Dr.1, Dr.2, Dθ.1, Dθ.2, Dφ.1, Dφ.2, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin,
    Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin]
  set F := fun x : ℂ × ℂ × ℂ => 𝒦 x.1 x.2.1 x.2.2 with hFdef
  set p : ℂ × ℂ × ℂ := (r * Complex.cos θ, r * Complex.sin θ * Complex.sin φ,
    r * Complex.sin θ * Complex.cos φ) with hpdef
  set H11 := fderiv ℂ (fderiv ℂ F) p (1, 0, 0) (1, 0, 0)
  set H22 := fderiv ℂ (fderiv ℂ F) p (0, 1, 0) (0, 1, 0)
  set H33 := fderiv ℂ (fderiv ℂ F) p (0, 0, 1) (0, 0, 1)
  set H23 := fderiv ℂ (fderiv ℂ F) p (0, 1, 0) (0, 0, 1)
  set g1 := fderiv ℂ F p (1, 0, 0)
  set g2 := fderiv ℂ F p (0, 1, 0)
  set g3 := fderiv ℂ F p (0, 0, 1)
  set C := Complex.cos θ
  set S := Complex.sin θ
  set c := Complex.cos φ
  set s := Complex.sin φ
  have hθ : S ^ 2 + C ^ 2 = 1 := Complex.sin_sq_add_cos_sq θ
  have hφ : s ^ 2 + c ^ 2 = 1 := Complex.sin_sq_add_cos_sq φ
  linear_combination (norm := skip) hP +
    (c * s * (C * H11 * S * r + C * H22 * S * r * s ^ 2 + 2 * C * H23 * S * c * r * s +
      C * H33 * S * c ^ 2 * r + 2 * C * c * δ * g3 + 2 * C * c * ε * g3 - C * c * g3 +
      2 * C * δ * g2 * s + 2 * C * ε * g2 * s - C * g2 * s + 2 * S * g1 * γ - S * g1) /
      (C * S * c * r * s)) * hθ +
    (C * (H22 * S * c * r * s + H33 * S * c * r * s + 2 * c * δ * g2 - c * g2 +
      2 * ε * g3 * s - g3 * s) / (C * S * c * r * s)) * hφ
  field_simp
  ring

/-- DLMF 31.10.20–31.10.21: in spherical coordinates `u = r cos θ`, `v = r sin θ sin φ`,
`w = r sin θ cos φ`, a solution of 31.10.18 satisfies
`𝒦_rr + ((2(γ+δ+ε)-1)/r)𝒦_r + 𝒦_θθ/r² + ((2(δ+ε)-1)cot θ - (2γ-1)tan θ)𝒦_θ/r²
+ 𝒦_φφ/(r² sin²θ) + ((2δ-1)cot φ - (2ε-1)tan φ)𝒦_φ/(r² sin²θ) = 0`. -/
@[dlmf 31.10.E20, dlmf 31.10.E21]
theorem heun_kernel_typeII_spherical {Ω : Set (ℂ × ℂ × ℂ)} (_hΩ : IsOpen Ω)
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
  exact heun_kernel_typeII_spherical' h𝒦 hpde hreg hpt

/-- First and second derivatives of `r ↦ r^m C` on the slit plane. -/
private lemma deriv_cpow_mul_const {r : ℂ} (m C : ℂ) (hr : r ∈ slitPlane) :
    deriv (fun r' => r' ^ m * C) r = m * r ^ (m - 1) * C ∧
      deriv (deriv fun r' => r' ^ m * C) r = m * (m - 1) * r ^ (m - 1 - 1) * C := by
  have hD : ∀ y ∈ slitPlane, HasDerivAt (fun r' => r' ^ m * C) (m * y ^ (m - 1) * C) y :=
    fun y hy => by
      convert ((hasDerivAt_id' y).cpow_const (c := m) hy).mul_const C using 1
      ring
  refine ⟨(hD r hr).deriv, ?_⟩
  have ev : deriv (fun r' => r' ^ m * C) =ᶠ[𝓝 r] fun y => m * y ^ (m - 1) * C :=
    eventually_of_mem (isOpen_slitPlane.mem_nhds hr) fun y hy => (hD y hy).deriv
  rw [ev.deriv_eq]
  have h := (((hasDerivAt_id' r).cpow_const (c := m - 1) hr).const_mul m).mul_const C
  refine h.deriv.trans ?_
  ring

/-- Chain rule for `t ↦ C · sin^q t · u(cos² t)`: first and second derivatives. -/
private lemma deriv_sin_cpow_cos_sq_comp {u : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hu : ContDiffOn ℂ 2 u U) (q C : ℂ) {t : ℂ} (ht : Complex.cos t ^ 2 ∈ U)
    (hs : Complex.sin t ∈ slitPlane) :
    deriv (fun t' => C * (Complex.sin t' ^ q * u (Complex.cos t' ^ 2))) t =
        C * (q * Complex.sin t ^ (q - 1) * Complex.cos t * u (Complex.cos t ^ 2) +
          Complex.sin t ^ q * (deriv u (Complex.cos t ^ 2) *
            (-2 * Complex.cos t * Complex.sin t))) ∧
      deriv (deriv fun t' => C * (Complex.sin t' ^ q * u (Complex.cos t' ^ 2))) t =
        C * ((q * (q - 1) * Complex.sin t ^ (q - 1 - 1) * Complex.cos t ^ 2 -
              q * Complex.sin t ^ (q - 1) * Complex.sin t) * u (Complex.cos t ^ 2) +
            2 * q * Complex.sin t ^ (q - 1) * Complex.cos t *
              (deriv u (Complex.cos t ^ 2) * (-2 * Complex.cos t * Complex.sin t)) +
            Complex.sin t ^ q * (deriv (deriv u) (Complex.cos t ^ 2) *
                (-2 * Complex.cos t * Complex.sin t) ^ 2 +
              deriv u (Complex.cos t ^ 2) *
                (2 * Complex.sin t ^ 2 - 2 * Complex.cos t ^ 2))) := by
  have hd : DifferentiableOn ℂ u U := hu.differentiableOn (by norm_num)
  have hd2 : DifferentiableOn ℂ (deriv u) U :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hU).1 hu).2.2.differentiableOn
      (by norm_num)
  have hh : ∀ s, HasDerivAt (fun t' => Complex.cos t' ^ 2)
      (-2 * Complex.cos s * Complex.sin s) s := fun s => by
    convert (Complex.hasDerivAt_cos s).pow 2 using 1
    simp
  have hW : IsOpen {s : ℂ | Complex.cos s ^ 2 ∈ U ∧ Complex.sin s ∈ slitPlane} :=
    (hU.preimage (by fun_prop)).inter (isOpen_slitPlane.preimage (by fun_prop))
  have hD : ∀ s ∈ {s : ℂ | Complex.cos s ^ 2 ∈ U ∧ Complex.sin s ∈ slitPlane},
      HasDerivAt (fun t' => C * (Complex.sin t' ^ q * u (Complex.cos t' ^ 2)))
        (C * (q * Complex.sin s ^ (q - 1) * Complex.cos s * u (Complex.cos s ^ 2) +
          Complex.sin s ^ q * (deriv u (Complex.cos s ^ 2) *
            (-2 * Complex.cos s * Complex.sin s)))) s := fun s hs' => by
    have h1 := (Complex.hasDerivAt_sin s).cpow_const (c := q) hs'.2
    have h2 := (hd.differentiableAt (hU.mem_nhds hs'.1)).hasDerivAt.comp s (hh s)
    have h3 : HasDerivAt (fun t' => C * (Complex.sin t' ^ q * u (Complex.cos t' ^ 2))) _ s :=
      (h1.mul h2).const_mul C
    exact h3
  refine ⟨(hD t ⟨ht, hs⟩).deriv, ?_⟩
  have ev : deriv (fun t' => C * (Complex.sin t' ^ q * u (Complex.cos t' ^ 2))) =ᶠ[𝓝 t]
      fun s => C * (q * Complex.sin s ^ (q - 1) * Complex.cos s * u (Complex.cos s ^ 2) +
          Complex.sin s ^ q * (deriv u (Complex.cos s ^ 2) *
            (-2 * Complex.cos s * Complex.sin s))) :=
    eventually_of_mem (hW.mem_nhds ⟨ht, hs⟩) fun s hs' => (hD s hs').deriv
  rw [ev.deriv_eq]
  have hs1 := (Complex.hasDerivAt_sin t).cpow_const (c := q - 1) hs
  have hs0 := (Complex.hasDerivAt_sin t).cpow_const (c := q) hs
  have hu0 := (hd.differentiableAt (hU.mem_nhds ht)).hasDerivAt.comp t (hh t)
  have hu1 := (hd2.differentiableAt (hU.mem_nhds ht)).hasDerivAt.comp t (hh t)
  have hc := ((Complex.hasDerivAt_cos t).const_mul (-2)).mul (Complex.hasDerivAt_sin t)
  have h := (((((hs1.const_mul q).mul (Complex.hasDerivAt_cos t)).mul hu0).add
    (hs0.mul (hu1.mul hc))).const_mul C)
  have h' : HasDerivAt (fun s => C * (q * Complex.sin s ^ (q - 1) * Complex.cos s *
      u (Complex.cos s ^ 2) + Complex.sin s ^ q * (deriv u (Complex.cos s ^ 2) *
        (-2 * Complex.cos s * Complex.sin s)))) _ t := h
  refine h'.deriv.trans ?_
  simp only [Function.comp_apply, Pi.mul_apply]
  ring

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
  intro L
  obtain ⟨hs, hc0, hs', hc'⟩ := hreg
  have hr0 : r ≠ 0 := slitPlane_ne_zero hr
  have eR : (fun r' => L r' θ φ) = fun r' => r' ^ m * (Complex.sin θ ^ (2 * p) *
      f (Complex.cos θ ^ 2) * g (Complex.cos φ ^ 2)) := funext fun _ => by simp only [L]; ring
  have eΘ : (fun θ' => L r θ' φ) = fun θ' => (r ^ m * g (Complex.cos φ ^ 2)) *
      (Complex.sin θ' ^ (2 * p) * f (Complex.cos θ' ^ 2)) := funext fun _ => by simp only [L]; ring
  have eΦ : L r θ = fun φ' => (r ^ m * Complex.sin θ ^ (2 * p) * f (Complex.cos θ ^ 2)) *
      g (Complex.cos φ' ^ 2) := rfl
  obtain ⟨d1, d2⟩ := deriv_cpow_mul_const m (Complex.sin θ ^ (2 * p) *
      f (Complex.cos θ ^ 2) * g (Complex.cos φ ^ 2)) hr
  obtain ⟨t1, t2⟩ := deriv_sin_cpow_cos_sq_comp hUf hf.1 (2 * p)
    (r ^ m * g (Complex.cos φ ^ 2)) hθ.1 hθ.2
  obtain ⟨e1, e2⟩ := deriv_cos_sq_comp hUg hg.1
    (r ^ m * Complex.sin θ ^ (2 * p) * f (Complex.cos θ ^ 2)) hφ
  rw [eR, eΘ, eΦ, d1, d2, t1, t2, e1, e2]
  have hsc := Complex.sin_sq_add_cos_sq θ
  have hsc' := Complex.sin_sq_add_cos_sq φ
  have hx1 : 1 - Complex.cos θ ^ 2 ≠ 0 := by
    rw [← hsc]; ring_nf; exact pow_ne_zero _ hs
  have hy1 : 1 - Complex.cos φ ^ 2 ≠ 0 := by
    rw [← hsc']; ring_nf; exact pow_ne_zero _ hs'
  have Rf := riemannNormalOperator_zero_zero_cleared (pow_ne_zero 2 hc0) hx1 (hf.2 _ hθ.1)
  have Rg := riemannNormalOperator_zero_zero_cleared (pow_ne_zero 2 hc') hy1 (hg.2 _ hφ)
  have er1 : r ^ (m - 1) = r ^ m / r := by rw [Complex.cpow_sub _ _ hr0, Complex.cpow_one]
  have er2 : r ^ (m - 1 - 1) = r ^ m / r ^ 2 := by
    rw [Complex.cpow_sub _ _ hr0, er1, Complex.cpow_one]; ring
  have es1 : Complex.sin θ ^ (2 * p - 1) = Complex.sin θ ^ (2 * p) / Complex.sin θ := by
    rw [Complex.cpow_sub _ _ hs, Complex.cpow_one]
  have es2 : Complex.sin θ ^ (2 * p - 1 - 1) = Complex.sin θ ^ (2 * p) / Complex.sin θ ^ 2 := by
    rw [Complex.cpow_sub _ _ hs, es1, Complex.cpow_one]; ring
  rw [er1, er2, es1, es2, Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin,
    Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin]
  have hε : ε = α + β + 1 - γ - δ := by linear_combination -hF
  have hB : B = α + β + 2 * p - A := by linear_combination hAB.1
  have hB' : B' = δ + ε - 1 - A' := by linear_combination hAB'.1
  have hσ₁ : σ₁ = m ^ 2 + 2 * (α + β) * m := by linear_combination -hm
  have hσ₂ : σ₂ = 4 * (p ^ 2 + (α + β - γ) * p) := by linear_combination -4 * hp
  have hAB2 := hAB.2
  have hAB2' := hAB'.2
  subst hc hB hB' hσ₁ hσ₂
  subst hε
  set F0 := f (Complex.cos θ ^ 2)
  set F1 := deriv f (Complex.cos θ ^ 2)
  set F2 := deriv (deriv f) (Complex.cos θ ^ 2)
  set G0 := g (Complex.cos φ ^ 2)
  set G1 := deriv g (Complex.cos φ ^ 2)
  set G2 := deriv (deriv g) (Complex.cos φ ^ 2)
  set Rm := r ^ m
  set Sq := Complex.sin θ ^ (2 * p)
  set co := Complex.cos θ
  set si := Complex.sin θ
  set co' := Complex.cos φ
  set si' := Complex.sin φ
  linear_combination (norm := skip)
    (Rm * Sq / (r ^ 2 * si ^ 2 * co * co' * si')) *
      ((4 * G0 * co * co' * si ^ 2 * si') * Rf + (4 * F0 * co * co' * si') * Rg +
        (4 * F0 * G0 * co * co' * si ^ 2 * si') * hAB2 + (4 * F0 * G0 * co * co' * si') * hAB2' +
        (4 * G0 * co * co' * si' * (F0 * α * p + F0 * β * p - F0 * γ * p + F0 * p ^ 2 +
          F1 * γ * si ^ 2 + F2 * co ^ 2 * si ^ 2)) * hsc +
        (4 * F0 * co * co' * si' * (G1 * α + G1 * β - G1 * δ - G1 * γ + G1 + G2 * co' ^ 2)) *
          hsc')
  field_simp
  ring

end DLMF.Heun
