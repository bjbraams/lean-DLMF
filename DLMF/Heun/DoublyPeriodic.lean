/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMF.JacobiElliptic.Basic
public import DLMF.Weierstrass.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Doubly-periodic forms of Heun's equation and Lamé's equation (DLMF §31.2(iv), §31.7(ii))

* Jacobi's elliptic form (31.2.7–31.2.8): with `a = k^{-2}` and `z = sn²(ζ, k)`, Heun's
  equation becomes an equation with coefficients in `sn, cn, dn` (the project's
  `DLMF.JacobiElliptic.jacobiSnk` etc., for `k` in `jacobiModulusDomain`).
* Weierstrass's form (31.2.9–31.2.12): for lattice data `H` with roots `e₁, e₂, e₃`, the variable
  `z = sn²(iK' + ξ(e₁ - e₃)^{1/2}, k)`, `k² = (e₂ - e₃)/(e₁ - e₃)`, equals
  `(℘(ξ) - e₃)/(e₂ - e₃)` (31.2.9; checked numerically), and Heun's equation with
  `a = (e₁ - e₃)/(e₂ - e₃)` becomes the Darboux–Treibich–Verdier type equation 31.2.11 for
  `W(ξ)`. The theorem is stated in the variable `(℘(ξ) - e₃)/(e₂ - e₃)`.
* Lamé's equation (31.7.5): with `a = k^{-2}`, `q = -ah/4`, `α = -ν/2`, `β = (ν+1)/2`,
  `γ = δ = ε = 1/2`, `w(ζ) = W(sn²ζ)` satisfies Lamé's equation
  `w'' + (h - ν(ν+1)k² sn²ζ) w = 0` (DLMF 29.2.1), stated in terms of the equation (proved from
  the Jacobi form). The solutions 31.3.1 and 31.3.5 give even and odd Lamé solutions. The
  remark that the specializations of §31.3(ii) give solutions near `ζ = K, K + iK', iK'` is not
  acquired.

Numerical checks (mpmath, `a = 2.3 + 0.7i`, complex parameters): 31.2.8 residual `3·10⁻³¹`;
the identity `sn²(iK' + ξ√(e₁-e₃), k) = (℘(ξ) - e₃)/(e₂ - e₃)` to `10⁻³⁰`; 31.2.11–31.2.12
residual `3·10⁻²⁹` (`e₁ = 1.1 + 0.2i`, `e₂ = -0.3 + 0.5i`).
-/

@[expose] public section

open Complex Filter Set
open DLMF.JacobiElliptic DLMF.Weierstrass
open scoped Topology Real

noncomputable section

namespace DLMF.Heun

variable {a q α β γ δ ε : ℂ}

/-- Pointwise equal coefficients give the same second-order equation. -/
theorem IsLinearODE2On.congr_coeff {p r p' r' w : ℂ → ℂ} {s : Set ℂ}
    (h : IsLinearODE2On p r w s) (hp : ∀ z ∈ s, p z = p' z) (hr : ∀ z ∈ s, r z = r' z) :
    IsLinearODE2On p' r' w s :=
  ⟨h.1, fun z hz => by rw [← hp z hz, ← hr z hz]; exact h.2 z hz⟩

/-! ### Jacobi's elliptic form -/

/-- DLMF 31.2.7–31.2.8, Jacobi's elliptic form: with `a = k^{-2}` and `z = sn²(ζ, k)`, a
solution `W` of Heun's equation gives a solution `w(ζ) = W(sn²(ζ, k))` of
`w'' + ((2γ-1) cn dn/sn - (2δ-1) sn dn/cn - (2ε-1)k² sn cn/dn) w' + 4k²(αβ sn² - q) w = 0`. -/
@[dlmf 31.2.E7, dlmf 31.2.E8]
theorem heun_jacobiForm {k : ℂ} (hk : k ∈ jacobiModulusDomain) (hF : α + β + 1 = γ + δ + ε)
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) {W : ℂ → ℂ}
    (hW : IsHeunSolOn (k ^ 2)⁻¹ q α β γ δ ε W U)
    (hVU : ∀ ζ ∈ V, jacobiSnk ζ k ^ 2 ∈ U ∧ jacobiSnk ζ k ≠ 0 ∧ jacobiCnk ζ k ≠ 0 ∧
      jacobiDnk ζ k ≠ 0) :
    IsLinearODE2On
      (fun ζ => (2 * γ - 1) * (jacobiCnk ζ k * jacobiDnk ζ k / jacobiSnk ζ k) -
        (2 * δ - 1) * (jacobiSnk ζ k * jacobiDnk ζ k / jacobiCnk ζ k) -
        (2 * ε - 1) * k ^ 2 * (jacobiSnk ζ k * jacobiCnk ζ k / jacobiDnk ζ k))
      (fun ζ => 4 * k ^ 2 * (α * β * jacobiSnk ζ k ^ 2 - q))
      (fun ζ => W (jacobiSnk ζ k ^ 2)) V := by
  sorry

/-! ### Weierstrass's form -/

/-- DLMF 31.2.9: with `k² = (e₂ - e₃)/(e₁ - e₃)` and `ζ = iK' + ξ(e₁ - e₃)^{1/2}`, the Jacobi
variable `z = sn²(ζ, k)` of 31.2.7 is `(℘(ξ) - e₃)/(e₂ - e₃)`; `e_j = ℘(ω_j)`,
`e₁ + e₂ + e₃ = 0`. Stated for `k` in `jacobiModulusDomain` and `ξ` off the lattice. -/
@[dlmf 31.2.E9]
theorem jacobiSnk_sq_eq_weierstrassP (H : HalfPeriods) {k : ℂ} (hk : k ∈ jacobiModulusDomain)
    (hk2 : k ^ 2 = (H.e 2 - H.e 3) / (H.e 1 - H.e 3)) {ξ : ℂ} (hξ : ξ ∉ H.lattice) :
    jacobiSnk (I * compEllIntKpk k + ξ * (H.e 1 - H.e 3) ^ (1 / 2 : ℂ)) k ^ 2 =
      (H.weierstrassP ξ - H.e 3) / (H.e 2 - H.e 3) := by
  sorry

/-- DLMF 31.2.9–31.2.12, Weierstrass's form: let `u` solve Heun's equation with
`a = (e₁ - e₃)/(e₂ - e₃)` and put `z(ξ) = (℘(ξ) - e₃)/(e₂ - e₃)` (31.2.9). Then
`W(ξ) = u(z(ξ)) / ((℘(ξ)-e₃)^{(1-2γ)/4} (℘(ξ)-e₂)^{(1-2δ)/4} (℘(ξ)-e₁)^{(1-2ε)/4})` (31.2.10,
principal powers) satisfies
`W'' + (H + b₀℘(ξ) + b₁℘(ξ+ω₁) + b₂℘(ξ+ω₂) + b₃℘(ξ+ω₃)) W = 0` (31.2.11) with
`b₀ = 4αβ - (γ+δ+ε-1/2)(γ+δ+ε-3/2)`, `b₁ = -(ε-1/2)(ε-3/2)`, `b₂ = -(δ-1/2)(δ-3/2)`,
`b₃ = -(γ-1/2)(γ-3/2)` and
`H = e₁(γ+δ-1)² + e₂(γ+ε-1)² + e₃(δ+ε-1)² - 4αβe₃ - 4q(e₂-e₃)` (31.2.12). -/
@[dlmf 31.2.E9, dlmf 31.2.E10, dlmf 31.2.E11, dlmf 31.2.E12]
theorem heun_weierstrassForm (L : HalfPeriods) (hF : α + β + 1 = γ + δ + ε) {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) {u : ℂ → ℂ}
    (hu : IsHeunSolOn ((L.e 1 - L.e 3) / (L.e 2 - L.e 3)) q α β γ δ ε u U)
    (hVU : ∀ ξ ∈ V, ξ ∉ L.lattice ∧ (L.weierstrassP ξ - L.e 3) / (L.e 2 - L.e 3) ∈ U ∧
      L.weierstrassP ξ - L.e 1 ∈ slitPlane ∧ L.weierstrassP ξ - L.e 2 ∈ slitPlane ∧
      L.weierstrassP ξ - L.e 3 ∈ slitPlane) :
    IsLinearODE2On 0
      (fun ξ => (L.e 1 * (γ + δ - 1) ^ 2 + L.e 2 * (γ + ε - 1) ^ 2 + L.e 3 * (δ + ε - 1) ^ 2 -
          4 * α * β * L.e 3 - 4 * q * (L.e 2 - L.e 3)) +
        (4 * α * β - (γ + δ + ε - 1 / 2) * (γ + δ + ε - 3 / 2)) * L.weierstrassP ξ -
        (ε - 1 / 2) * (ε - 3 / 2) * L.weierstrassP (ξ + L.ω₁) -
        (δ - 1 / 2) * (δ - 3 / 2) * L.weierstrassP (ξ + L.ω₂) -
        (γ - 1 / 2) * (γ - 3 / 2) * L.weierstrassP (ξ + L.ω₃))
      (fun ξ => u ((L.weierstrassP ξ - L.e 3) / (L.e 2 - L.e 3)) /
        ((L.weierstrassP ξ - L.e 3) ^ ((1 - 2 * γ) / 4) *
          (L.weierstrassP ξ - L.e 2) ^ ((1 - 2 * δ) / 4) *
          (L.weierstrassP ξ - L.e 1) ^ ((1 - 2 * ε) / 4))) V := by
  sorry

/-! ### Lamé's equation (§31.7(ii)) -/

/-- DLMF 31.7.5: with `a = k^{-2}`, `q = -ah/4`, `α = -ν/2`, `β = (ν+1)/2`,
`γ = δ = ε = 1/2`, Heun's equation in the variable `z = sn²(ζ, k)` becomes Lamé's equation
`w'' + (h - ν(ν+1)k² sn²(ζ, k)) w = 0` (DLMF 29.2.1). Proved from the Jacobi form 31.2.8. -/
@[dlmf 31.7.E5, dlmf 31.7.ii]
theorem heun_lame {k h ν : ℂ} (hk : k ∈ jacobiModulusDomain) (hk0 : k ≠ 0) {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) {W : ℂ → ℂ}
    (hW : IsHeunSolOn (k ^ 2)⁻¹ (-((k ^ 2)⁻¹ * h / 4)) (-ν / 2) ((ν + 1) / 2) (1 / 2) (1 / 2)
      (1 / 2) W U)
    (hVU : ∀ ζ ∈ V, jacobiSnk ζ k ^ 2 ∈ U ∧ jacobiSnk ζ k ≠ 0 ∧ jacobiCnk ζ k ≠ 0 ∧
      jacobiDnk ζ k ≠ 0) :
    IsLinearODE2On 0 (fun ζ => h - ν * (ν + 1) * k ^ 2 * jacobiSnk ζ k ^ 2)
      (fun ζ => W (jacobiSnk ζ k ^ 2)) V := by
  refine (heun_jacobiForm hk (by ring) hU hV hW hVU).congr_coeff (fun ζ _ => ?_)
    (fun ζ _ => ?_)
  · simp only [Pi.zero_apply]; ring
  · field_simp
    ring

/-- DLMF §31.7(ii): the local solutions 31.3.1 and 31.3.5 at `z = 0` become, with the parameters
31.7.5, an even and an odd solution of Lamé's equation near `ζ = 0`:
`Hl(k^{-2}, -h/(4k²); -ν/2, (ν+1)/2, 1/2, 1/2; sn²ζ)` and
`sn ζ · Hl(k^{-2}, (k^{-2} + 1)/4 - h/(4k²); (1-ν)/2, (ν+2)/2, 3/2, 1/2; sn²ζ)` (the factor
`z^{1-γ} = z^{1/2}` taken as `sn ζ`). -/
@[dlmf 31.7.ii]
theorem heunLocal_lame_even_odd {k h ν : ℂ} (hk : k ∈ jacobiModulusDomain) (hk0 : k ≠ 0) :
    ∃ V ∈ 𝓝 (0 : ℂ),
      (IsLinearODE2On 0 (fun ζ => h - ν * (ν + 1) * k ^ 2 * jacobiSnk ζ k ^ 2)
        (fun ζ => heunLocal (k ^ 2)⁻¹ (-((k ^ 2)⁻¹ * h / 4)) (-ν / 2) ((ν + 1) / 2) (1 / 2)
          (1 / 2) (jacobiSnk ζ k ^ 2)) V ∧
      IsLinearODE2On 0 (fun ζ => h - ν * (ν + 1) * k ^ 2 * jacobiSnk ζ k ^ 2)
        (fun ζ => jacobiSnk ζ k * heunLocal (k ^ 2)⁻¹ (((k ^ 2)⁻¹ + 1) / 4 - (k ^ 2)⁻¹ * h / 4)
          ((1 - ν) / 2) ((ν + 2) / 2) (3 / 2) (1 / 2) (jacobiSnk ζ k ^ 2)) V) ∧
      ∀ ζ ∈ V, -ζ ∈ V →
        heunLocal (k ^ 2)⁻¹ (-((k ^ 2)⁻¹ * h / 4)) (-ν / 2) ((ν + 1) / 2) (1 / 2) (1 / 2)
            (jacobiSnk (-ζ) k ^ 2) =
          heunLocal (k ^ 2)⁻¹ (-((k ^ 2)⁻¹ * h / 4)) (-ν / 2) ((ν + 1) / 2) (1 / 2) (1 / 2)
            (jacobiSnk ζ k ^ 2) ∧
        jacobiSnk (-ζ) k = -jacobiSnk ζ k := by
  sorry

end DLMF.Heun
