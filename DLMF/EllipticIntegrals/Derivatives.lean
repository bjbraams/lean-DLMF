/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.LegendreIdentities

/-!
# Derivatives and differential equations of Legendre's integrals (DLMF §19.4)

Complex-modulus forms of DLMF 19.4.1–19.4.9. Here `k'² = 1 - k²`. The complete integrals are
differentiated on the principal domain `{k ≠ 0, 1 - k² ∈ ℂ \ (-∞, 0]}`; the incomplete ones at
a complex amplitude `φ` whose path `[0, φ]` keeps `1 - k² sin²θ` in `ℂ \ (-∞, 0]`
(`legendrePathOK`), with `Δ = (1 - k² sin²φ)^{1/2}`. The real-parameter forms (in `m = k²`) are
the existing `DLMF.Elliptic.Real.hasDerivAt_compEllIntKm`, `Real.hasDerivAt_compEllIntEm`,
`Real.hasDerivAt_compEllIntKm_sq` and `Real.hasDerivAt_compEllIntEm_sq` (tagged 19.4.E1–E2).

The second relations of 19.4.1, 19.4.2 and the formulas 19.4.3 are proved from the first
relations; the first relations, 19.4.4–19.4.9 (differentiation under the integral sign) are
admitted. The hypergeometric equations of the prose (19.4.ii) follow from 19.4.8–19.4.9.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic

/-- The path condition for Legendre's integrals at amplitude `φ`: `1 - k² sin²θ` stays in
`ℂ \ (-∞, 0]` along the segment `[0, φ]`, so the integrand is holomorphic near the path. -/
def legendrePathOK (φ k : ℂ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, 1 - k ^ 2 * Complex.sin (t * φ) ^ 2 ∈ slitPlane

/-- For a real amplitude the path condition follows from `1 - k² ∈ ℂ \ (-∞, 0]`. -/
theorem legendrePathOK_ofReal {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) (φ : ℝ) :
    legendrePathOK φ k := fun t _ => by
  simpa using ei19a_one_sub_sq_mul_sin_sq_mem_slitPlane hk (t * φ)

/-- The principal domain of `K` and `E` as a differentiable function: `k ≠ 0`, `k² ∉ [1, ∞)`. -/
def compEllIntDomain : Set ℂ := {k | k ≠ 0 ∧ 1 - k ^ 2 ∈ slitPlane}

theorem isOpen_compEllIntDomain : IsOpen compEllIntDomain := by
  exact (isOpen_ne (x := (0 : ℂ))).inter
    (Complex.isOpen_slitPlane.preimage (by fun_prop : Continuous fun k : ℂ => 1 - k ^ 2))

/-! ### §19.4(i) Derivatives -/

/-- **Admitted.** DLMF 19.4.1 (first relation): `dK/dk = (E - k'²K)/(k k'²)` on the principal
domain. -/
@[dlmf 19.4.E1]
theorem hasDerivAt_compEllIntKk {k : ℂ} (hk : k ∈ compEllIntDomain) :
    HasDerivAt compEllIntKk
      ((compEllIntEk k - (1 - k ^ 2) * compEllIntKk k) / (k * (1 - k ^ 2))) k := by
  sorry

/-- **Admitted.** DLMF 19.4.2 (first relation): `dE/dk = (E - K)/k` on the principal domain. -/
@[dlmf 19.4.E2]
theorem hasDerivAt_compEllIntEk {k : ℂ} (hk : k ∈ compEllIntDomain) :
    HasDerivAt compEllIntEk ((compEllIntEk k - compEllIntKk k) / k) k := by
  sorry

theorem ei19a_one_sub_sq_ne_zero {k : ℂ} (hk : k ∈ compEllIntDomain) : 1 - k ^ 2 ≠ 0 :=
  slitPlane_ne_zero hk.2

/-- DLMF 19.4.1 (second relation): `d(E - k'²K)/dk = kK`. -/
@[dlmf 19.4.E1]
theorem hasDerivAt_compEllIntEk_sub {k : ℂ} (hk : k ∈ compEllIntDomain) :
    HasDerivAt (fun k => compEllIntEk k - (1 - k ^ 2) * compEllIntKk k) (k * compEllIntKk k) k := by
  have h := (hasDerivAt_compEllIntEk hk).sub
    (((hasDerivAt_pow 2 k).const_sub 1).mul (hasDerivAt_compEllIntKk hk))
  convert h using 1
  have h0 := hk.1
  have h1 := ei19a_one_sub_sq_ne_zero hk
  field_simp
  ring

/-- DLMF 19.4.2 (second relation): `d(E - K)/dk = -kE/k'²`. -/
@[dlmf 19.4.E2]
theorem hasDerivAt_compEllIntEk_sub_compEllIntKk {k : ℂ} (hk : k ∈ compEllIntDomain) :
    HasDerivAt (fun k => compEllIntEk k - compEllIntKk k)
      (-(k * compEllIntEk k) / (1 - k ^ 2)) k := by
  have h := (hasDerivAt_compEllIntEk hk).sub (hasDerivAt_compEllIntKk hk)
  convert h using 1
  have h0 := hk.1
  have h1 := ei19a_one_sub_sq_ne_zero hk
  field_simp
  ring

/-- DLMF 19.4.3: `d²E/dk² = -(1/k) dK/dk = (k'²K - E)/(k²k'²)` on the principal domain. -/
@[dlmf 19.4.E3]
theorem deriv_deriv_compEllIntEk {k : ℂ} (hk : k ∈ compEllIntDomain) :
    deriv (deriv compEllIntEk) k = -(1 / k) * deriv compEllIntKk k ∧
      deriv (deriv compEllIntEk) k =
        ((1 - k ^ 2) * compEllIntKk k - compEllIntEk k) / (k ^ 2 * (1 - k ^ 2)) := by
  have hev : deriv compEllIntEk =ᶠ[𝓝 k] fun k => (compEllIntEk k - compEllIntKk k) / k :=
    Filter.eventually_of_mem (isOpen_compEllIntDomain.mem_nhds hk) fun z hz =>
      (hasDerivAt_compEllIntEk hz).deriv
  have hd : HasDerivAt (fun k => (compEllIntEk k - compEllIntKk k) / k)
      ((-(k * compEllIntEk k) / (1 - k ^ 2) * k - (compEllIntEk k - compEllIntKk k) * 1) /
        k ^ 2) k :=
    (hasDerivAt_compEllIntEk_sub_compEllIntKk hk).div (hasDerivAt_id k) hk.1
  rw [hev.deriv_eq, hd.deriv, (hasDerivAt_compEllIntKk hk).deriv]
  have h0 := hk.1
  have h1 := ei19a_one_sub_sq_ne_zero hk
  constructor <;> (field_simp; ring)

/-- **Admitted.** DLMF 19.4.4:
`∂Π(α², k)/∂k = k/(k'²(k² - α²)) (E(k) - k'²Π(α², k))` on the principal domain, for `α² ≠ k²`
with `1 - α² ∈ ℂ \ (-∞, 0]` (no principal value). -/
@[dlmf 19.4.E4]
theorem hasDerivAt_compEllIntPik {α2 k : ℂ} (hk : k ∈ compEllIntDomain)
    (hα : 1 - α2 ∈ slitPlane) (hαk : k ^ 2 ≠ α2) :
    HasDerivAt (fun k => compEllIntPik α2 k) (k / ((1 - k ^ 2) * (k ^ 2 - α2)) *
      (compEllIntEk k - (1 - k ^ 2) * compEllIntPik α2 k)) k := by
  sorry

/-- **Admitted.** DLMF 19.4.5:
`∂F(φ, k)/∂k = (E(φ, k) - k'²F(φ, k))/(k k'²) - k sin φ cos φ/(k'² Δ)`, `Δ = √(1 - k² sin²φ)`,
for `k ≠ 0`, `k² ≠ 1` and a path `[0, φ]` satisfying `legendrePathOK`. -/
@[dlmf 19.4.E5]
theorem hasDerivAt_incEllIntFk {φ k : ℂ} (hk0 : k ≠ 0) (hk1 : k ^ 2 ≠ 1)
    (hφ : legendrePathOK φ k) :
    HasDerivAt (fun k => incEllIntFk φ k)
      ((incEllIntEk φ k - (1 - k ^ 2) * incEllIntFk φ k) / (k * (1 - k ^ 2)) -
        k * Complex.sin φ * Complex.cos φ /
          ((1 - k ^ 2) * (1 - k ^ 2 * Complex.sin φ ^ 2) ^ (1 / 2 : ℂ))) k := by
  sorry

/-- **Admitted.** DLMF 19.4.6: `∂E(φ, k)/∂k = (E(φ, k) - F(φ, k))/k` for `k ≠ 0` and a path
satisfying `legendrePathOK`. -/
@[dlmf 19.4.E6]
theorem hasDerivAt_incEllIntEk {φ k : ℂ} (hk0 : k ≠ 0) (hφ : legendrePathOK φ k) :
    HasDerivAt (fun k => incEllIntEk φ k) ((incEllIntEk φ k - incEllIntFk φ k) / k) k := by
  sorry

/-- **Admitted.** DLMF 19.4.7:
`∂Π(φ, α², k)/∂k = k/(k'²(k² - α²)) (E(φ, k) - k'²Π(φ, α², k) - k² sin φ cos φ/Δ)`, for `k ≠ 0`,
`k² ≠ 1`, `k² ≠ α²`, a path satisfying `legendrePathOK` on which `1 - α² sin²θ ≠ 0`. -/
@[dlmf 19.4.E7]
theorem hasDerivAt_incEllIntPik {φ α2 k : ℂ} (hk0 : k ≠ 0) (hk1 : k ^ 2 ≠ 1) (hαk : k ^ 2 ≠ α2)
    (hφ : legendrePathOK φ k) (hα : ∀ t ∈ Icc (0 : ℝ) 1, 1 - α2 * Complex.sin (t * φ) ^ 2 ≠ 0) :
    HasDerivAt (fun k => incEllIntPik φ α2 k) (k / ((1 - k ^ 2) * (k ^ 2 - α2)) *
      (incEllIntEk φ k - (1 - k ^ 2) * incEllIntPik φ α2 k -
        k ^ 2 * Complex.sin φ * Complex.cos φ /
          (1 - k ^ 2 * Complex.sin φ ^ 2) ^ (1 / 2 : ℂ))) k := by
  sorry

/-! ### §19.4(ii) Differential equations -/

/-- **Admitted.** DLMF 19.4.8: with `D_k = ∂/∂k`,
`(k k'² D_k² + (1 - 3k²) D_k - k) F(φ, k) = -k sin φ cos φ/(1 - k² sin²φ)^{3/2}`, for `k ≠ 0`,
`k² ≠ 1` and a path satisfying `legendrePathOK`. -/
@[dlmf 19.4.E8]
theorem incEllIntFk_ode {φ k : ℂ} (hk0 : k ≠ 0) (hk1 : k ^ 2 ≠ 1) (hφ : legendrePathOK φ k) :
    k * (1 - k ^ 2) * deriv (deriv fun k => incEllIntFk φ k) k +
        (1 - 3 * k ^ 2) * deriv (fun k => incEllIntFk φ k) k - k * incEllIntFk φ k =
      -(k * Complex.sin φ * Complex.cos φ) / (1 - k ^ 2 * Complex.sin φ ^ 2) ^ (3 / 2 : ℂ) := by
  sorry

/-- **Admitted.** DLMF 19.4.9:
`(k k'² D_k² + k'² D_k + k) E(φ, k) = k sin φ cos φ/√(1 - k² sin²φ)`, for `k ≠ 0`, `k² ≠ 1` and a
path satisfying `legendrePathOK`. -/
@[dlmf 19.4.E9]
theorem incEllIntEk_ode {φ k : ℂ} (hk0 : k ≠ 0) (hk1 : k ^ 2 ≠ 1) (hφ : legendrePathOK φ k) :
    k * (1 - k ^ 2) * deriv (deriv fun k => incEllIntEk φ k) k +
        (1 - k ^ 2) * deriv (fun k => incEllIntEk φ k) k + k * incEllIntEk φ k =
      k * Complex.sin φ * Complex.cos φ / (1 - k ^ 2 * Complex.sin φ ^ 2) ^ (1 / 2 : ℂ) := by
  sorry

/-- DLMF §19.4(ii) (prose): at `φ = π/2`, 19.4.8 and 19.4.9 become the hypergeometric equations
(15.10.1, in the variable `k²`) of `K` and `E`:
`k k'² K'' + (1 - 3k²) K' - kK = 0` and `k k'² E'' + k'² E' + kE = 0` on the principal domain
(from the admitted 19.4.8–19.4.9). -/
@[dlmf 19.4.ii]
theorem compEllIntKk_compEllIntEk_ode {k : ℂ} (hk : k ∈ compEllIntDomain) :
    k * (1 - k ^ 2) * deriv (deriv compEllIntKk) k + (1 - 3 * k ^ 2) * deriv compEllIntKk k -
        k * compEllIntKk k = 0 ∧
      k * (1 - k ^ 2) * deriv (deriv compEllIntEk) k + (1 - k ^ 2) * deriv compEllIntEk k +
        k * compEllIntEk k = 0 := by
  have hk1 : k ^ 2 ≠ 1 := fun h => ei19a_one_sub_sq_ne_zero hk (by rw [h]; ring)
  have hp : legendrePathOK (π / 2) k := by
    have := legendrePathOK_ofReal hk.2 (π / 2)
    simpa using this
  have hcos : Complex.cos (π / 2) = 0 := by
    rw [show ((π : ℂ) / 2) = ((π / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
      Real.cos_pi_div_two, ofReal_zero]
  have hK : compEllIntKk = fun k => incEllIntFk (π / 2) k := funext compEllIntKk_eq_incEllIntFk
  have hE : compEllIntEk = fun k => incEllIntEk (π / 2) k := rfl
  constructor
  · have h := incEllIntFk_ode hk.1 hk1 hp
    rw [hcos] at h
    rw [hK]
    simpa using h
  · have h := incEllIntEk_ode hk.1 hk1 hp
    rw [hcos] at h
    rw [hE]
    simpa using h

end DLMF.EllipticIntegrals
