/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Basic
public import DLMF.Theta.Basic
public import DLMF.JacobiElliptic.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Relations to theta and Jacobian elliptic functions (DLMF §23.6)

Theta functions are the project's lattice-parameter forms `θⱼ(z|τ)`
(`DLMF.Elliptic.jacobiThetaOneTau … jacobiThetaFourTau`), which are DLMF's `θⱼ(z, q)` with
`q = e^{iπτ}`; using `τ = ω₃/ω₁` directly avoids the branch of `q^{1/4}` (which is written
`e^{iπτ/4}` below). Derivatives at `0` are Lean derivatives in `z`
(`DLMF.Theta.jacobiThetaOneDerivNullTau`, `iteratedDeriv 3`), and `d/dz ln θ₁` is the
logarithmic derivative `θ₁'/θ₁`.

**Jacobian functions (§23.6(ii)).** DLMF states 23.6.16–23.6.26 for *any* pair of generators
with `K = K(k)` the complete elliptic integral of the modulus. The squared quantities in
23.6.17 hold for every pair of generators only if `K` denotes the lattice quarter period
`K = (π/2)θ₃²(0|τ)` (`DLMF.JacobiElliptic.compEllIntKTau`), not the principal integral of
`k = θ₂²/θ₃²`: `k²` is invariant under `τ ↦ τ/(2τ + 1)` while `ω₁²(e₁ - e₃)` is not
(numerical check: `ω₁ = 1.1 + 0.2i`, `ω₃ = 0.3 + 0.9i`, generators `(ω₁ + 2ω₃, ω₃)` give
`K(k)² - ω₁²(e₁ - e₃) ≈ 11.0 - 13.7i`). The lattice forms are therefore acquired for all
generators, and the literal principal form under the hypothesis `τ = iK'(k)/K(k)`.

**Source correction.** In 23.6.29 the last term has the wrong sign: the correct identity is
`ζ(z|𝕃₃) - ζ(z + 2iK'|𝕃₃) + ζ(2iK'|𝕃₃) = cs(z, k)` (the printed `- ζ(2iK'|𝕃₃)` fails
numerically, e.g. by `-0.49i` for `k² = 0.3`, `z = 0.37 + 0.21i`; the corrected form agrees to
`10⁻¹⁰`). The correction also follows from the oddness of `cs` and `ζ` and 23.2.11.
-/

@[expose] public section

open Complex PeriodPair DLMF.Elliptic DLMF.Theta DLMF.JacobiElliptic MeasureTheory
open scoped Real

noncomputable section

namespace DLMF.Weierstrass

namespace HalfPeriods

variable (H : HalfPeriods)

/-! ### Theta functions (§23.6(i)) -/

/-- `θ₁'''(0|τ)`. -/
def thetaOneTripleDerivNull (τ : ℂ) : ℂ := iteratedDeriv 3 (fun z ↦ jacobiThetaOneTau z τ) 0

/-- DLMF 23.6.2: `e₁ = π²/(12ω₁²) (θ₂⁴(0,q) + 2θ₄⁴(0,q))`. -/
@[dlmf 23.6.E2]
theorem e_one_eq_theta :
    H.e 1 = π ^ 2 / (12 * H.ω₁ ^ 2) *
      (jacobiThetaTwoTau 0 H.tau ^ 4 + 2 * jacobiThetaFourTau 0 H.tau ^ 4) := by
  sorry

/-- DLMF 23.6.3: `e₂ = π²/(12ω₁²) (θ₂⁴(0,q) - θ₄⁴(0,q))`. -/
@[dlmf 23.6.E3]
theorem e_two_eq_theta :
    H.e 2 = π ^ 2 / (12 * H.ω₁ ^ 2) *
      (jacobiThetaTwoTau 0 H.tau ^ 4 - jacobiThetaFourTau 0 H.tau ^ 4) := by
  sorry

/-- DLMF 23.6.4: `e₃ = -π²/(12ω₁²) (2θ₂⁴(0,q) + θ₄⁴(0,q))`. -/
@[dlmf 23.6.E4]
theorem e_three_eq_theta :
    H.e 3 = -(π ^ 2 / (12 * H.ω₁ ^ 2)) *
      (2 * jacobiThetaTwoTau 0 H.tau ^ 4 + jacobiThetaFourTau 0 H.tau ^ 4) := by
  sorry

/-- DLMF 23.6.5: `℘(z) - e₁ = (π θ₃(0,q) θ₄(0,q) θ₂(πz/(2ω₁),q) / (2ω₁ θ₁(πz/(2ω₁),q)))²`,
`z ∉ 𝕃`. -/
@[dlmf 23.6.E5]
theorem weierstrassP_sub_e_one_eq_theta {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 1 =
      (π * jacobiThetaThreeTau 0 H.tau * jacobiThetaFourTau 0 H.tau *
          jacobiThetaTwoTau (π * z / (2 * H.ω₁)) H.tau /
        (2 * H.ω₁ * jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau)) ^ 2 := by
  sorry

/-- DLMF 23.6.6: `℘(z) - e₂ = (π θ₂(0,q) θ₄(0,q) θ₃(πz/(2ω₁),q) / (2ω₁ θ₁(πz/(2ω₁),q)))²`,
`z ∉ 𝕃`. -/
@[dlmf 23.6.E6]
theorem weierstrassP_sub_e_two_eq_theta {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 2 =
      (π * jacobiThetaTwoTau 0 H.tau * jacobiThetaFourTau 0 H.tau *
          jacobiThetaThreeTau (π * z / (2 * H.ω₁)) H.tau /
        (2 * H.ω₁ * jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau)) ^ 2 := by
  sorry

/-- DLMF 23.6.7: `℘(z) - e₃ = (π θ₂(0,q) θ₃(0,q) θ₄(πz/(2ω₁),q) / (2ω₁ θ₁(πz/(2ω₁),q)))²`,
`z ∉ 𝕃`. -/
@[dlmf 23.6.E7]
theorem weierstrassP_sub_e_three_eq_theta {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 3 =
      (π * jacobiThetaTwoTau 0 H.tau * jacobiThetaThreeTau 0 H.tau *
          jacobiThetaFourTau (π * z / (2 * H.ω₁)) H.tau /
        (2 * H.ω₁ * jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau)) ^ 2 := by
  sorry

/-- DLMF 23.6.8: `η₁ = -(π²/(12ω₁)) θ₁'''(0,q)/θ₁'(0,q)`. -/
@[dlmf 23.6.E8]
theorem eta_one_eq_theta :
    H.eta 1 = -(π ^ 2 / (12 * H.ω₁)) *
      (thetaOneTripleDerivNull H.tau / jacobiThetaOneDerivNullTau H.tau) := by
  sorry

/-- DLMF 23.6.9: `σ(z) = 2ω₁ exp(η₁z²/(2ω₁)) θ₁(πz/(2ω₁),q)/(π θ₁'(0,q))`, `z ∈ ℂ`. -/
@[dlmf 23.6.E9]
theorem weierstrassSigma_eq_theta (z : ℂ) :
    H.weierstrassSigma z = 2 * H.ω₁ * cexp (H.eta 1 * z ^ 2 / (2 * H.ω₁)) *
      jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau / (π * jacobiThetaOneDerivNullTau H.tau) := by
  sorry

/-- DLMF 23.6.10: `σ(ω₁) = 2ω₁ exp(η₁ω₁/2) θ₂(0,q)/(π θ₁'(0,q))`. -/
@[dlmf 23.6.E10]
theorem weierstrassSigma_ω₁_eq_theta :
    H.weierstrassSigma H.ω₁ = 2 * H.ω₁ * cexp (H.eta 1 * H.ω₁ / 2) * jacobiThetaTwoTau 0 H.tau /
      (π * jacobiThetaOneDerivNullTau H.tau) := by
  sorry

/-- DLMF 23.6.11: `σ(ω₂) = -2ω₁ exp(η₁(ω₁τ² + ω₃ - ω₂)/2) θ₃(0,q)/(π q^{1/4} θ₁'(0,q))`,
with `q^{1/4} = e^{iπτ/4}`. -/
@[dlmf 23.6.E11]
theorem weierstrassSigma_ω₂_eq_theta :
    H.weierstrassSigma H.ω₂ = -(2 * H.ω₁) *
      cexp (H.eta 1 * (H.ω₁ * H.tau ^ 2 + H.ω₃ - H.ω₂) / 2) * jacobiThetaThreeTau 0 H.tau /
        (π * cexp (π * I * H.tau / 4) * jacobiThetaOneDerivNullTau H.tau) := by
  sorry

/-- DLMF 23.6.12: `σ(ω₃) = 2iω₁ exp(η₁ω₁τ²/2) θ₄(0,q)/(π q^{1/4} θ₁'(0,q))`, with
`q^{1/4} = e^{iπτ/4}`. -/
@[dlmf 23.6.E12]
theorem weierstrassSigma_ω₃_eq_theta :
    H.weierstrassSigma H.ω₃ = 2 * I * H.ω₁ * cexp (H.eta 1 * H.ω₁ * H.tau ^ 2 / 2) *
      jacobiThetaFourTau 0 H.tau /
        (π * cexp (π * I * H.tau / 4) * jacobiThetaOneDerivNullTau H.tau) := by
  sorry

/-- DLMF 23.6.13: with `z = πu/(2ω₁)`, `ζ(u) = η₁u/ω₁ + (π/(2ω₁)) d/dz ln θ₁(z,q)`,
`u ∉ 𝕃`. -/
@[dlmf 23.6.E13]
theorem weierstrassZeta_eq_theta {u : ℂ} (hu : u ∉ H.lattice) :
    H.weierstrassZeta u = H.eta 1 / H.ω₁ * u + π / (2 * H.ω₁) *
      (deriv (fun z ↦ jacobiThetaOneTau z H.tau) (π * u / (2 * H.ω₁)) /
        jacobiThetaOneTau (π * u / (2 * H.ω₁)) H.tau) := by
  sorry

/-- DLMF 23.6.14: with `z = πu/(2ω₁)`,
`℘(u) = (π/(2ω₁))² (θ₁'''(0,q)/(3θ₁'(0,q)) - d²/dz² ln θ₁(z,q))`, `u ∉ 𝕃`. -/
@[dlmf 23.6.E14]
theorem weierstrassP_eq_theta {u : ℂ} (hu : u ∉ H.lattice) :
    H.weierstrassP u = (π / (2 * H.ω₁)) ^ 2 *
      (thetaOneTripleDerivNull H.tau / (3 * jacobiThetaOneDerivNullTau H.tau) -
        deriv (fun z ↦ deriv (fun w ↦ jacobiThetaOneTau w H.tau) z / jacobiThetaOneTau z H.tau)
          (π * u / (2 * H.ω₁))) := by
  sorry

/-- DLMF 23.6.15: with `z = πu/(2ω₁)`, for `j = 1, 2, 3`,
`σ(u + ω_j)/σ(ω_j) = exp(η_ju + η₁u²/(2ω₁)) θ_{j+1}(z,q)/θ_{j+1}(0,q)`, `u ∈ ℂ`. -/
@[dlmf 23.6.E15]
theorem weierstrassSigma_add_halfPeriod_eq_theta (u : ℂ) {j : ℕ}
    (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    H.weierstrassSigma (u + H.halfPeriod j) / H.weierstrassSigma (H.halfPeriod j) =
      cexp (H.eta j * u + H.eta 1 * u ^ 2 / (2 * H.ω₁)) *
        jacobiThetaTau (j + 1) (π * u / (2 * H.ω₁)) H.tau / jacobiThetaTau (j + 1) 0 H.tau := by
  sorry

/-! ### Jacobian elliptic functions (§23.6(ii)) -/

/-- The lattice quarter period `K = (π/2)θ₃²(0|τ)` of the half-periods. -/
abbrev quarterK : ℂ := compEllIntKTau H.tau
/-- The lattice modulus `k = θ₂²(0|τ)/θ₃²(0|τ)`. -/
abbrev modulus : ℂ := jacobiModulusTau H.tau
/-- The lattice complementary modulus `k' = θ₄²(0|τ)/θ₃²(0|τ)`. -/
abbrev comodulus : ℂ := jacobiComodulusTau H.tau

/-- DLMF 23.6.16: `k² = (e₂ - e₃)/(e₁ - e₃)` and `k'² = (e₁ - e₂)/(e₁ - e₃)`. -/
@[dlmf 23.6.E16]
theorem modulus_sq_eq :
    H.modulus ^ 2 = (H.e 2 - H.e 3) / (H.e 1 - H.e 3) ∧
      H.comodulus ^ 2 = (H.e 1 - H.e 2) / (H.e 1 - H.e 3) := by
  sorry

/-- DLMF 23.6.17 (lattice form, all pairs of generators): with `K = (π/2)θ₃²(0|τ)` and
`K' = -iτK`, `K² = ω₁²(e₁ - e₃)` and `K'² = ω₃²(e₃ - e₁)`.
Corrected from the printed DLMF formula: the printed form uses the principal `K(k)`, which
fails for some generator pairs; with the lattice `K = (π/2)θ₃²(0|τ)` it holds for all. -/
@[dlmf 23.6.E17]
theorem quarterK_sq_eq :
    H.quarterK ^ 2 = H.ω₁ ^ 2 * (H.e 1 - H.e 3) ∧
      compEllIntKpTau H.tau ^ 2 = H.ω₃ ^ 2 * (H.e 3 - H.e 1) := by
  sorry

/-- DLMF 23.6.17 (literal form): if the generators are such that `τ = iK'(k)/K(k)` for a
modulus `k` with `ℜk > 0`, `k ∉ [1, ∞)` (principal complete integrals), then
`K(k)² = ω₁²(e₁ - e₃)` and `K(k')² = ω₃²(e₃ - e₁)`.
Corrected from the printed DLMF formula: with the principal `K(k)` the printed identity fails
for some pairs of generators, so the hypothesis `τ = iK'(k)/K(k)` is added; the lattice form
`quarterK_sq_eq` holds for every pair (see the module docstring). -/
@[dlmf 23.6.E17]
theorem compEllIntKk_sq_eq {k : ℂ} (hk : k ∈ jacobiModulusDomain) (hτ : jacobiTauk k = H.tau) :
    compEllIntKk k ^ 2 = H.ω₁ ^ 2 * (H.e 1 - H.e 3) ∧
      compEllIntKpk k ^ 2 = H.ω₃ ^ 2 * (H.e 3 - H.e 1) := by
  sorry

/-- DLMF 23.6.18: `e₁ = K²(1 + k'²)/(3ω₁²)`. -/
@[dlmf 23.6.E18]
theorem e_one_eq_jacobi :
    H.e 1 = H.quarterK ^ 2 / (3 * H.ω₁ ^ 2) * (1 + H.comodulus ^ 2) := by
  sorry

/-- DLMF 23.6.19: `e₂ = K²(k² - k'²)/(3ω₁²)`. -/
@[dlmf 23.6.E19]
theorem e_two_eq_jacobi :
    H.e 2 = H.quarterK ^ 2 / (3 * H.ω₁ ^ 2) * (H.modulus ^ 2 - H.comodulus ^ 2) := by
  sorry

/-- DLMF 23.6.20: `e₃ = -K²(1 + k²)/(3ω₁²)`. -/
@[dlmf 23.6.E20]
theorem e_three_eq_jacobi :
    H.e 3 = -(H.quarterK ^ 2 / (3 * H.ω₁ ^ 2)) * (1 + H.modulus ^ 2) := by
  sorry

/-- DLMF 23.6.21: `℘(z) - e₁ = (K²/ω₁²) cs²(Kz/ω₁, k)`, `z ∉ 𝕃`. -/
@[dlmf 23.6.E21]
theorem weierstrassP_sub_e_one_eq_cs {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 1 =
      H.quarterK ^ 2 / H.ω₁ ^ 2 * jacobiCsTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  sorry

/-- DLMF 23.6.22: `℘(z) - e₂ = (K²/ω₁²) ds²(Kz/ω₁, k)`, `z ∉ 𝕃`. -/
@[dlmf 23.6.E22]
theorem weierstrassP_sub_e_two_eq_ds {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 2 =
      H.quarterK ^ 2 / H.ω₁ ^ 2 * jacobiDsTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  sorry

/-- DLMF 23.6.23: `℘(z) - e₃ = (K²/ω₁²) ns²(Kz/ω₁, k)`, `z ∉ 𝕃`. -/
@[dlmf 23.6.E23]
theorem weierstrassP_sub_e_three_eq_ns {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 3 =
      H.quarterK ^ 2 / H.ω₁ ^ 2 * jacobiNsTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  sorry

/-- DLMF 23.6.24: `℘(z + ω₁) - e₁ = (Kk'/ω₁)² sc²(Kz/ω₁, k)`, `z + ω₁ ∉ 𝕃`. -/
@[dlmf 23.6.E24]
theorem weierstrassP_add_ω₁_sub_e_one_eq_sc {z : ℂ} (hz : z + H.ω₁ ∉ H.lattice) :
    H.weierstrassP (z + H.ω₁) - H.e 1 =
      (H.quarterK * H.comodulus / H.ω₁) ^ 2 * jacobiScTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  sorry

/-- DLMF 23.6.25: `℘(z + ω₂) - e₂ = -(Kkk'/ω₁)² sd²(Kz/ω₁, k)`, `z + ω₂ ∉ 𝕃`. -/
@[dlmf 23.6.E25]
theorem weierstrassP_add_ω₂_sub_e_two_eq_sd {z : ℂ} (hz : z + H.ω₂ ∉ H.lattice) :
    H.weierstrassP (z + H.ω₂) - H.e 2 =
      -(H.quarterK * H.modulus * H.comodulus / H.ω₁) ^ 2 *
        jacobiSdTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  sorry

/-- DLMF 23.6.26: `℘(z + ω₃) - e₃ = (Kk/ω₁)² sn²(Kz/ω₁, k)`, `z + ω₃ ∉ 𝕃`. -/
@[dlmf 23.6.E26]
theorem weierstrassP_add_ω₃_sub_e_three_eq_sn {z : ℂ} (hz : z + H.ω₃ ∉ H.lattice) :
    H.weierstrassP (z + H.ω₃) - H.e 3 =
      (H.quarterK * H.modulus / H.ω₁) ^ 2 * jacobiSnTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  sorry

end HalfPeriods

/-- DLMF 23.6.27: for a modulus `k` (`ℜk > 0`, `k ∉ [1, ∞)`), `K = K(k)`, `K' = K(k')` and
`𝕃₁` the lattice with generators `4K, 2iK'`,
`ζ(z|𝕃₁) - ζ(z + 2K|𝕃₁) + ζ(2K|𝕃₁) = ns(z, k)` for `z, z + 2K ∉ 𝕃₁`. -/
@[dlmf 23.6.E27]
theorem weierstrassZeta_ns {k : ℂ} (hk : k ∈ jacobiModulusDomain) (L : PeriodPair)
    (h₁ : L.ω₁ = 4 * compEllIntKk k) (h₂ : L.ω₂ = 2 * I * compEllIntKpk k) {z : ℂ}
    (hz : z ∉ L.lattice) (hz' : z + 2 * compEllIntKk k ∉ L.lattice) :
    weierstrassZeta L z - weierstrassZeta L (z + 2 * compEllIntKk k) +
      weierstrassZeta L (2 * compEllIntKk k) = jacobiNsk z k := by
  sorry

/-- DLMF 23.6.28: with `𝕃₂` generated by `2K - 2iK'`, `2K + 2iK'`,
`ζ(z|𝕃₂) - ζ(z + 2K|𝕃₂) + ζ(2K|𝕃₂) = ds(z, k)` for `z, z + 2K ∉ 𝕃₂`. -/
@[dlmf 23.6.E28]
theorem weierstrassZeta_ds {k : ℂ} (hk : k ∈ jacobiModulusDomain) (L : PeriodPair)
    (h₁ : L.ω₁ = 2 * compEllIntKk k - 2 * I * compEllIntKpk k)
    (h₂ : L.ω₂ = 2 * compEllIntKk k + 2 * I * compEllIntKpk k) {z : ℂ}
    (hz : z ∉ L.lattice) (hz' : z + 2 * compEllIntKk k ∉ L.lattice) :
    weierstrassZeta L z - weierstrassZeta L (z + 2 * compEllIntKk k) +
      weierstrassZeta L (2 * compEllIntKk k) = jacobiDsk z k := by
  sorry

/-- DLMF 23.6.29, **corrected sign**: with `𝕃₃` generated by `2K`, `4iK'`,
`ζ(z|𝕃₃) - ζ(z + 2iK'|𝕃₃) + ζ(2iK'|𝕃₃) = cs(z, k)` for `z, z + 2iK' ∉ 𝕃₃`.
Corrected from the printed DLMF formula: DLMF prints `- ζ(2iK'|𝕃₃)` for the last term, which
is false (difference about `-0.49i` at `k² = 0.3`; see the module docstring). -/
@[dlmf 23.6.E29]
theorem weierstrassZeta_cs {k : ℂ} (hk : k ∈ jacobiModulusDomain) (L : PeriodPair)
    (h₁ : L.ω₁ = 2 * compEllIntKk k) (h₂ : L.ω₂ = 4 * I * compEllIntKpk k) {z : ℂ}
    (hz : z ∉ L.lattice) (hz' : z + 2 * I * compEllIntKpk k ∉ L.lattice) :
    weierstrassZeta L z - weierstrassZeta L (z + 2 * I * compEllIntKpk k) +
      weierstrassZeta L (2 * I * compEllIntKpk k) = jacobiCsk z k := by
  sorry

/-! ### Elliptic integrals (§23.6(iv)) -/

namespace HalfPeriods

variable (H : HalfPeriods)

/-- The real lattice roots `e_j` of a rectangular lattice, as real numbers. -/
abbrev eRe (j : ℕ) : ℝ := (H.e j).re

/-- DLMF 23.6.30: for a rectangular lattice (`ω₁ = a > 0`, `ω₃ = ib`, `b > 0`) and
`z = x ∈ (0, ω₁]`, `t = ℘(z)` is real, `t ≥ e₁` and
`z = ½ ∫_t^∞ du/√((u - e₁)(u - e₂)(u - e₃))`. -/
@[dlmf 23.6.E30]
theorem rectangular_integral_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hω₁ : H.ω₁ = a)
    (hω₃ : H.ω₃ = b * I) {x : ℝ} (hx : x ∈ Set.Ioc 0 a) :
    (H.weierstrassP x).im = 0 ∧ H.eRe 1 ≤ (H.weierstrassP x).re ∧
      x = 1 / 2 * ∫ u in Set.Ioi (H.weierstrassP x).re,
        1 / Real.sqrt ((u - H.eRe 1) * (u - H.eRe 2) * (u - H.eRe 3)) := by
  sorry

/-- DLMF 23.6.31: rectangular lattice, `z = ω₁ + iy ∈ [ω₁, ω₁ + ω₃]`: `t = ℘(z)` is real,
`e₂ ≤ t ≤ e₁` and `z - ω₁ = (i/2) ∫_t^{e₁} du/√((e₁ - u)(u - e₂)(u - e₃))`. -/
@[dlmf 23.6.E31]
theorem rectangular_integral_two {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hω₁ : H.ω₁ = a)
    (hω₃ : H.ω₃ = b * I) {y : ℝ} (hy : y ∈ Set.Icc 0 b) :
    (H.weierstrassP (a + y * I)).im = 0 ∧ H.eRe 2 ≤ (H.weierstrassP (a + y * I)).re ∧
      (H.weierstrassP (a + y * I)).re ≤ H.eRe 1 ∧
      ((a + y * I : ℂ) - H.ω₁) = I / 2 * ((∫ u in (H.weierstrassP (a + y * I)).re..H.eRe 1,
        1 / Real.sqrt ((H.eRe 1 - u) * (u - H.eRe 2) * (u - H.eRe 3)) : ℝ) : ℂ) := by
  sorry

/-- DLMF 23.6.32: rectangular lattice, `z = ω₃ + x ∈ [ω₃, ω₁ + ω₃]`: `t = ℘(z)` is real,
`e₃ ≤ t ≤ e₂` and `z - ω₃ = ½ ∫_{e₃}^t du/√((e₁ - u)(e₂ - u)(u - e₃))`. -/
@[dlmf 23.6.E32]
theorem rectangular_integral_three {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hω₁ : H.ω₁ = a)
    (hω₃ : H.ω₃ = b * I) {x : ℝ} (hx : x ∈ Set.Icc 0 a) :
    (H.weierstrassP (x + b * I)).im = 0 ∧ H.eRe 3 ≤ (H.weierstrassP (x + b * I)).re ∧
      (H.weierstrassP (x + b * I)).re ≤ H.eRe 2 ∧
      ((x + b * I : ℂ) - H.ω₃) = ((1 / 2 * ∫ u in H.eRe 3..(H.weierstrassP (x + b * I)).re,
        1 / Real.sqrt ((H.eRe 1 - u) * (H.eRe 2 - u) * (u - H.eRe 3)) : ℝ) : ℂ) := by
  sorry

/-- DLMF 23.6.33: rectangular lattice, `z = iy ∈ (0, ω₃]`: `t = ℘(z)` is real, `t ≤ e₃` and
`z = (i/2) ∫_{-∞}^t du/√((e₁ - u)(e₂ - u)(e₃ - u))`. -/
@[dlmf 23.6.E33]
theorem rectangular_integral_four {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hω₁ : H.ω₁ = a)
    (hω₃ : H.ω₃ = b * I) {y : ℝ} (hy : y ∈ Set.Ioc 0 b) :
    (H.weierstrassP (y * I)).im = 0 ∧ (H.weierstrassP (y * I)).re ≤ H.eRe 3 ∧
      (y * I : ℂ) = I / 2 * ((∫ u in Set.Iio (H.weierstrassP (y * I)).re,
        1 / Real.sqrt ((H.eRe 1 - u) * (H.eRe 2 - u) * (H.eRe 3 - u)) : ℝ) : ℂ) := by
  sorry

/-- DLMF 23.6.34: rectangular lattice,
`2ω₁ = ∫_{e₁}^∞ du/√((u - e₁)(u - e₂)(u - e₃)) = ∫_{e₃}^{e₂} du/√((e₁ - u)(e₂ - u)(u - e₃))`. -/
@[dlmf 23.6.E34]
theorem rectangular_two_ω₁ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hω₁ : H.ω₁ = a)
    (hω₃ : H.ω₃ = b * I) :
    2 * a = ∫ u in Set.Ioi (H.eRe 1),
        1 / Real.sqrt ((u - H.eRe 1) * (u - H.eRe 2) * (u - H.eRe 3)) ∧
      2 * a = ∫ u in H.eRe 3..H.eRe 2,
        1 / Real.sqrt ((H.eRe 1 - u) * (H.eRe 2 - u) * (u - H.eRe 3)) := by
  sorry

/-- DLMF 23.6.35: rectangular lattice, `2ω₃ = i ∫_{e₂}^{e₁} du/√((e₁ - u)(u - e₂)(u - e₃))
= i ∫_{-∞}^{e₃} du/√((e₁ - u)(e₂ - u)(e₃ - u))`; with `ω₃ = ib` this says `2b` equals both
integrals. -/
@[dlmf 23.6.E35]
theorem rectangular_two_ω₃ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hω₁ : H.ω₁ = a)
    (hω₃ : H.ω₃ = b * I) :
    2 * b = ∫ u in H.eRe 2..H.eRe 1,
        1 / Real.sqrt ((H.eRe 1 - u) * (u - H.eRe 2) * (u - H.eRe 3)) ∧
      2 * b = ∫ u in Set.Iio (H.eRe 3),
        1 / Real.sqrt ((H.eRe 1 - u) * (H.eRe 2 - u) * (H.eRe 3 - u)) := by
  sorry

end HalfPeriods

/-- DLMF 23.6.36 (general lattice): let `z ≠ e₁, e₂, e₃`, let `γ : [0, ∞) → ℂ` be a `C¹` path
from `z` to `∞` avoiding `e₁, e₂, e₃`, and let `s` be a continuous determination along `γ` of
`√(4u³ - g₂u - g₃)`. Then `w = ∫_γ du/s(u)` converges and `℘(w) = z`. The value of `w` depends
on the path and the determination of the square root. -/
@[dlmf 23.6.E36]
theorem weierstrassP_inverse_integral (H : HalfPeriods) (γ : ℝ → ℂ) (s : ℝ → ℂ)
    (hγ : ContDiff ℝ 1 γ) (hγ0 : ∀ t, 0 ≤ t → ∀ j ∈ ({1, 2, 3} : Finset ℕ), γ t ≠ H.e j)
    (hγinf : Filter.Tendsto (fun t ↦ ‖γ t‖) Filter.atTop Filter.atTop)
    (hs : ContinuousOn s (Set.Ici 0))
    (hs2 : ∀ t, 0 ≤ t → s t ^ 2 = 4 * γ t ^ 3 - H.g₂ * γ t - H.g₃) :
    ∃ w : ℂ, Filter.Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, deriv γ t / s t) Filter.atTop
        (nhds w) ∧ H.weierstrassP w = γ 0 := by
  sorry

end DLMF.Weierstrass
