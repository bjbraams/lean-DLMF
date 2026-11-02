/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Relations.ThetaIdentities
public import DLMF.JacobiElliptic.EisensteinSeries

/-!
# Relations between Weierstrass and Jacobian elliptic functions

Theta representations of `ζ`, `℘` and `σ` (DLMF 23.6.13–23.6.15), their specialization to
Jacobian elliptic functions (DLMF §23.6(ii)), the Weierstrass functions of the lattices
attached to a modulus (DLMF 23.6.27–23.6.29), and the inversion of `℘` by integrals
(DLMF §23.6(iv)).

## Main definitions

* `quarterK`, `modulus`, `comodulus`: the lattice quantities `K = (π/2)θ₃²(0|τ)`,
  `k = θ₂²/θ₃²` and `k' = θ₄²/θ₃²` at `z = 0`.
* `eRe`: the real lattice roots of a rectangular lattice.

## Main results

* `weierstrassZeta_eq_theta`, `weierstrassP_eq_theta`, `weierstrassSigma_add_halfPeriod_eq_theta`:
  DLMF 23.6.13–23.6.15.
* `modulus_sq_eq`, `quarterK_sq_eq`, `compEllIntKk_sq_eq`: DLMF 23.6.16–23.6.17, in lattice form
  for all generators and in the literal principal form.
* `e_one_eq_jacobi`, `e_two_eq_jacobi`, `e_three_eq_jacobi`: DLMF 23.6.18–23.6.20.
* `weierstrassP_sub_e_one_eq_cs`, `weierstrassP_sub_e_two_eq_ds`,
  `weierstrassP_sub_e_three_eq_ns`: DLMF 23.6.21–23.6.23.
* `weierstrassP_add_ω₁_sub_e_one_eq_sc`, `weierstrassP_add_ω₂_sub_e_two_eq_sd`,
  `weierstrassP_add_ω₃_sub_e_three_eq_sn`: DLMF 23.6.24–23.6.26.
* `weierstrassZeta_ns`, `weierstrassZeta_ds`, `weierstrassZeta_cs`: DLMF 23.6.27–23.6.29, the
  last with corrected sign.
* `rectangular_integral_one` … `rectangular_integral_four`: DLMF 23.6.30–23.6.33.
* `rectangular_two_ω₁`, `rectangular_two_ω₃`: DLMF 23.6.34–23.6.35.
* `weierstrassP_inverse_integral`: DLMF 23.6.36 for a general lattice.

## Implementation notes

Principal-modulus and lattice-quarter-period forms keep their respective domain assumptions;
see the module docstring of `DLMF.Weierstrass.Relations` for the conventions and the
correction of 23.6.29.
-/

@[expose] public section

open Complex PeriodPair DLMF.Elliptic DLMF.Theta DLMF.JacobiElliptic MeasureTheory

open scoped Real

open Filter Topology

noncomputable section

namespace DLMF.Weierstrass

open DLMF.EllipticIntegrals (compEllIntKk compEllIntKpk)

namespace HalfPeriods

variable (H : HalfPeriods)

/-- DLMF 23.6.13: with `z = πu/(2ω₁)`, `ζ(u) = η₁u/ω₁ + (π/(2ω₁)) d/dz ln θ₁(z,q)`,
`u ∉ 𝕃`. -/
@[dlmf 23.6.E13]
theorem weierstrassZeta_eq_theta {u : ℂ} (hu : u ∉ H.lattice) :
    H.weierstrassZeta u = H.eta 1 / H.ω₁ * u + π / (2 * H.ω₁) *
      (deriv (fun z ↦ jacobiThetaOneTau z H.tau) (π * u / (2 * H.ω₁)) /
        jacobiThetaOneTau (π * u / (2 * H.ω₁)) H.tau) := by
  exact H.weierstrassZeta_eq_jacobiThetaOneTau_logDeriv hu

/-- DLMF 23.6.14: with `z = πu/(2ω₁)`,
`℘(u) = (π/(2ω₁))² (θ₁'''(0,q)/(3θ₁'(0,q)) - d²/dz² ln θ₁(z,q))`, `u ∉ 𝕃`. -/
@[dlmf 23.6.E14]
theorem weierstrassP_eq_theta {u : ℂ} (hu : u ∉ H.lattice) :
    H.weierstrassP u = (π / (2 * H.ω₁)) ^ 2 *
      (thetaOneTripleDerivNull H.tau / (3 * jacobiThetaOneDerivNullTau H.tau) -
        deriv (fun z ↦ deriv (fun w ↦ jacobiThetaOneTau w H.tau) z / jacobiThetaOneTau z H.tau)
          (π * u / (2 * H.ω₁))) := by
  have hω := H.ω₁_ne_zero
  have hD := H.jacobiThetaOneDerivNullTau_tau_ne_zero
  rw [H.weierstrassP_eq_neg_deriv_jacobiThetaOneTau_logDeriv hu, H.eta_one_eq_thetaOneTripleDerivNull]
  field_simp
  ring

/-- DLMF 23.6.15: with `z = πu/(2ω₁)`, for `j = 1, 2, 3`,
`σ(u + ω_j)/σ(ω_j) = exp(η_ju + η₁u²/(2ω₁)) θ_{j+1}(z,q)/θ_{j+1}(0,q)`, `u ∈ ℂ`. -/
@[dlmf 23.6.E15]
theorem weierstrassSigma_add_halfPeriod_eq_theta (u : ℂ) {j : ℕ}
    (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    H.weierstrassSigma (u + H.halfPeriod j) / H.weierstrassSigma (H.halfPeriod j) =
      cexp (H.eta j * u + H.eta 1 * u ^ 2 / (2 * H.ω₁)) *
        jacobiThetaTau (j + 1) (π * u / (2 * H.ω₁)) H.tau / jacobiThetaTau (j + 1) 0 H.tau := by
  have hω := H.ω₁_ne_zero
  have hD := H.jacobiThetaOneDerivNullTau_tau_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  have hL := H.weierstrassSigma_eq_weierstrassSigmaTheta_and_eta_three.2
  have hsum := H.eta_one_add_eta_two_add_eta_three
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  set w := π * u / (2 * H.ω₁) with hw
  rcases hj with rfl | rfl | rfl
  · rw [H.weierstrassSigma_eq_weierstrassSigmaTheta_and_eta_three.1, H.weierstrassSigma_eq_weierstrassSigmaTheta_and_eta_three.1, weierstrassSigmaTheta, weierstrassSigmaTheta,
      halfPeriod_one,
      show π * (u + H.ω₁) / (2 * H.ω₁) = w + π / 2 by rw [hw]; field_simp,
      show π * H.ω₁ / (2 * H.ω₁) = 0 + π / 2 by rw [zero_add]; field_simp,
      (jacobiThetaOneTau_add_sub_half_pi _ _).1, (jacobiThetaOneTau_add_sub_half_pi _ _).1]
    simp only [jacobiThetaTau]
    have e : cexp (H.eta 1 * (u + H.ω₁) ^ 2 / (2 * H.ω₁)) =
        cexp (H.eta 1 * u + H.eta 1 * u ^ 2 / (2 * H.ω₁)) *
          cexp (H.eta 1 * H.ω₁ ^ 2 / (2 * H.ω₁)) := by
      rw [← exp_add]; congr 1; field_simp; ring
    rw [e]
    have := exp_ne_zero (H.eta 1 * H.ω₁ ^ 2 / (2 * H.ω₁))
    field_simp
  · -- `j = 2`
    set c : ℂ := π / 2 + π * H.tau / 2 with hc
    have a1 := (jacobiThetaOneTau_half_periods (w - c) H.tau).2.2
    have a0 := (jacobiThetaOneTau_half_periods (0 - c) H.tau).2.2
    rw [show w - c + π / 2 + π * H.tau / 2 = w by rw [hc]; ring] at a1
    rw [show 0 - c + π / 2 + π * H.tau / 2 = 0 by rw [hc]; ring] at a0
    rw [H.weierstrassSigma_eq_weierstrassSigmaTheta_and_eta_three.1, H.weierstrassSigma_eq_weierstrassSigmaTheta_and_eta_three.1, weierstrassSigmaTheta, weierstrassSigmaTheta,
      halfPeriod_two,
      show π * (u + H.ω₂) / (2 * H.ω₁) = w - c by
        rw [hw, hc, HalfPeriods.tau, HalfPeriods.ω₂]; field_simp; ring,
      show π * H.ω₂ / (2 * H.ω₁) = 0 - c by
        rw [hc, HalfPeriods.tau, HalfPeriods.ω₂]; field_simp; ring, a1, a0]
    simp only [jacobiThetaTau]
    have e : cexp (H.eta 1 * (u + H.ω₂) ^ 2 / (2 * H.ω₁)) * thetaMultiplierM (w - c) H.tau =
        cexp (H.eta 2 * u + H.eta 1 * u ^ 2 / (2 * H.ω₁)) *
          (cexp (H.eta 1 * H.ω₂ ^ 2 / (2 * H.ω₁)) * thetaMultiplierM (0 - c) H.tau) := by
      simp only [thetaMultiplierM, ← exp_add]
      congr 1
      rw [show H.eta 2 = -H.eta 1 - H.eta 3 by linear_combination hsum, ← hL, hw]
      rw [HalfPeriods.ω₂]
      field_simp
      ring
    have hM0 : thetaMultiplierM (0 - c) H.tau ≠ 0 := exp_ne_zero _
    have hE0 := exp_ne_zero (H.eta 1 * H.ω₂ ^ 2 / (2 * H.ω₁))
    generalize cexp (H.eta 1 * (u + H.ω₂) ^ 2 / (2 * H.ω₁)) = E1 at *
    generalize thetaMultiplierM (w - c) H.tau = M1 at *
    generalize cexp (H.eta 2 * u + H.eta 1 * u ^ 2 / (2 * H.ω₁)) = X at *
    generalize cexp (H.eta 1 * H.ω₂ ^ 2 / (2 * H.ω₁)) = E0 at *
    generalize thetaMultiplierM (0 - c) H.tau = M0 at *
    field_simp
    linear_combination jacobiThetaThreeTau w H.tau * e
  · -- `j = 3`
    have b1 := (jacobiThetaFourTau_half_periods w H.tau).2.1
    have b0 := (jacobiThetaFourTau_half_periods 0 H.tau).2.1
    rw [H.weierstrassSigma_eq_weierstrassSigmaTheta_and_eta_three.1, H.weierstrassSigma_eq_weierstrassSigmaTheta_and_eta_three.1, weierstrassSigmaTheta, weierstrassSigmaTheta,
      halfPeriod_three,
      show π * (u + H.ω₃) / (2 * H.ω₁) = w + π * H.tau / 2 by
        rw [hw, HalfPeriods.tau]; field_simp,
      show π * H.ω₃ / (2 * H.ω₁) = 0 + π * H.tau / 2 by
        rw [HalfPeriods.tau, zero_add]; field_simp]
    simp only [jacobiThetaTau]
    rw [b1, b0]
    have hT0 : jacobiThetaOneTau (0 + π * H.tau / 2) H.tau ≠ 0 := by
      intro h0; rw [h0, mul_zero] at b0; exact n4 b0
    have e : cexp (H.eta 1 * (u + H.ω₃) ^ 2 / (2 * H.ω₁)) * thetaMultiplierM 0 H.tau =
        cexp (H.eta 3 * u + H.eta 1 * u ^ 2 / (2 * H.ω₁)) *
          (thetaMultiplierM w H.tau * cexp (H.eta 1 * H.ω₃ ^ 2 / (2 * H.ω₁))) := by
      simp only [thetaMultiplierM, ← exp_add]
      congr 1
      rw [← hL, hw]
      field_simp
      ring
    have hM0 : thetaMultiplierM 0 H.tau ≠ 0 := exp_ne_zero _
    have hMw : thetaMultiplierM w H.tau ≠ 0 := exp_ne_zero _
    have hE0 := exp_ne_zero (H.eta 1 * H.ω₃ ^ 2 / (2 * H.ω₁))
    generalize cexp (H.eta 1 * (u + H.ω₃) ^ 2 / (2 * H.ω₁)) = E1 at *
    generalize thetaMultiplierM w H.tau = Mw at *
    generalize cexp (H.eta 3 * u + H.eta 1 * u ^ 2 / (2 * H.ω₁)) = X at *
    generalize cexp (H.eta 1 * H.ω₃ ^ 2 / (2 * H.ω₁)) = E0 at *
    generalize thetaMultiplierM 0 H.tau = M0 at *
    generalize jacobiThetaOneTau (w + π * H.tau / 2) H.tau = T1 at *
    generalize jacobiThetaOneTau (0 + π * H.tau / 2) H.tau = T0 at *
    field_simp
    linear_combination T1 * e

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
  obtain ⟨d3, d2⟩ := H.e_one_sub_e_three_and_e_one_sub_e_two
  have hj := jacobiThetaNull_fourth_power H.tau H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at hj
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  have hω := H.ω₁_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show H.e 2 - H.e 3 = (H.e 1 - H.e 3) - (H.e 1 - H.e 2) by ring, d3, d2,
    modulus, comodulus, jacobiModulusTau, jacobiComodulusTau]
  constructor
  · field_simp
    linear_combination -hj
  · field_simp

/-- DLMF 23.6.17 (lattice form, all pairs of generators): with `K = (π/2)θ₃²(0|τ)` and
`K' = -iτK`, `K² = ω₁²(e₁ - e₃)` and `K'² = ω₃²(e₃ - e₁)`.
Corrected from the printed DLMF formula: the printed form uses the principal `K(k)`, which
fails for some generator pairs; with the lattice `K = (π/2)θ₃²(0|τ)` it holds for all. -/
@[dlmf 23.6.E17]
theorem quarterK_sq_eq :
    H.quarterK ^ 2 = H.ω₁ ^ 2 * (H.e 1 - H.e 3) ∧
      compEllIntKpTau H.tau ^ 2 = H.ω₃ ^ 2 * (H.e 3 - H.e 1) := by
  obtain ⟨d3, -⟩ := H.e_one_sub_e_three_and_e_one_sub_e_two
  have hω := H.ω₁_ne_zero
  constructor
  · rw [d3, quarterK, compEllIntKTau]; field_simp
  · rw [show H.e 3 - H.e 1 = -(H.e 1 - H.e 3) by ring, d3, compEllIntKpTau, compEllIntKTau,
      HalfPeriods.tau]
    field_simp
    rw [I_sq]
    ring

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
  obtain ⟨-, -, hK⟩ := jacobi_inversion_k hk
  rw [hτ] at hK
  obtain ⟨q1, q2⟩ := H.quarterK_sq_eq
  have hK0 : compEllIntKk k ≠ 0 := by
    rw [← hK, compEllIntKTau]
    exact mul_ne_zero (by simp [Real.pi_ne_zero]) (pow_ne_zero _ (jacobiThetaThreeTau_zero_ne_zero H.tau_im_pos))
  have hKp : compEllIntKpk k = compEllIntKpTau H.tau := by
    rw [compEllIntKpTau, hK, ← hτ, jacobiTauk]
    field_simp
    rw [I_sq]; ring
  refine ⟨?_, ?_⟩
  · rw [← hK]; exact q1
  · rw [hKp]; exact q2

/-- DLMF 23.6.18: `e₁ = K²(1 + k'²)/(3ω₁²)`. -/
@[dlmf 23.6.E18]
theorem e_one_eq_jacobi :
    H.e 1 = H.quarterK ^ 2 / (3 * H.ω₁ ^ 2) * (1 + H.comodulus ^ 2) := by
  have h := H.e_one_eq_theta
  have hj := jacobiThetaNull_fourth_power H.tau H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at hj
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  have hω := H.ω₁_ne_zero
  rw [h, quarterK, comodulus, compEllIntKTau, jacobiComodulusTau]
  field_simp
  linear_combination (-12 : ℂ) * hj

/-- DLMF 23.6.19: `e₂ = K²(k² - k'²)/(3ω₁²)`. -/
@[dlmf 23.6.E19]
theorem e_two_eq_jacobi :
    H.e 2 = H.quarterK ^ 2 / (3 * H.ω₁ ^ 2) * (H.modulus ^ 2 - H.comodulus ^ 2) := by
  have h := H.e_two_eq_theta
  have hj := jacobiThetaNull_fourth_power H.tau H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at hj
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  have hω := H.ω₁_ne_zero
  rw [h, quarterK, comodulus, modulus, compEllIntKTau, jacobiComodulusTau, jacobiModulusTau]
  field_simp
  ring

/-- DLMF 23.6.20: `e₃ = -K²(1 + k²)/(3ω₁²)`. -/
@[dlmf 23.6.E20]
theorem e_three_eq_jacobi :
    H.e 3 = -(H.quarterK ^ 2 / (3 * H.ω₁ ^ 2)) * (1 + H.modulus ^ 2) := by
  have h := H.e_three_eq_theta
  have hj := jacobiThetaNull_fourth_power H.tau H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at hj
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  have hω := H.ω₁_ne_zero
  rw [h, quarterK, modulus, compEllIntKTau, jacobiModulusTau]
  field_simp
  linear_combination (12 : ℂ) * hj

/-- The Jacobi theta argument at `Kz/ω₁` is `πz/(2ω₁)`. -/
private lemma jacobiZetaTau_quarterK_mul_div (z : ℂ) :
    jacobiZetaTau (H.quarterK * z / H.ω₁) H.tau = π * z / (2 * H.ω₁) := by
  have hω := H.ω₁_ne_zero
  have n3 := (jacobiThetaNullTau_ne_zero H.tau_im_pos).2.1
  simp only [jacobiThetaThreeNullTau] at n3
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [jacobiZetaTau, quarterK, compEllIntKTau]
  field_simp

/-- `θ₁(w) ≠ 0` at `w = πz/(2ω₁)` for `z ∉ 𝕃`. -/
theorem jacobiThetaOneTau_pi_mul_div_ne_zero {z : ℂ} (hz : z ∉ H.lattice) :
    jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau ≠ 0 := by
  intro h0; apply hz; apply (H.weierstrassSigmaTheta_eq_zero_iff z).mp
  simp only [weierstrassSigmaTheta, h0, mul_zero, zero_div]

/-- DLMF 23.6.21: `℘(z) - e₁ = (K²/ω₁²) cs²(Kz/ω₁, k)`, `z ∉ 𝕃`. -/
@[dlmf 23.6.E21]
theorem weierstrassP_sub_e_one_eq_cs {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 1 =
      H.quarterK ^ 2 / H.ω₁ ^ 2 * jacobiCsTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hθ := H.jacobiThetaOneTau_pi_mul_div_ne_zero hz
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  rw [H.weierstrassP_sub_e_one_eq_jacobiTheta_sq hz, jacobiCsTau, jacobiPQTau, H.jacobiZetaTau_quarterK_mul_div]
  simp only [jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ite_false, quarterK, compEllIntKTau]
  field_simp

/-- DLMF 23.6.22: `℘(z) - e₂ = (K²/ω₁²) ds²(Kz/ω₁, k)`, `z ∉ 𝕃`. -/
@[dlmf 23.6.E22]
theorem weierstrassP_sub_e_two_eq_ds {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 2 =
      H.quarterK ^ 2 / H.ω₁ ^ 2 * jacobiDsTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hθ := H.jacobiThetaOneTau_pi_mul_div_ne_zero hz
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  rw [H.weierstrassP_sub_e_two_eq_jacobiTheta_sq hz, jacobiDsTau, jacobiPQTau, H.jacobiZetaTau_quarterK_mul_div]
  simp only [jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ite_false, quarterK, compEllIntKTau]
  field_simp

/-- DLMF 23.6.23: `℘(z) - e₃ = (K²/ω₁²) ns²(Kz/ω₁, k)`, `z ∉ 𝕃`. -/
@[dlmf 23.6.E23]
theorem weierstrassP_sub_e_three_eq_ns {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 3 =
      H.quarterK ^ 2 / H.ω₁ ^ 2 * jacobiNsTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hθ := H.jacobiThetaOneTau_pi_mul_div_ne_zero hz
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  rw [H.weierstrassP_sub_e_three_eq_jacobiTheta_sq hz, jacobiNsTau, jacobiPQTau, H.jacobiZetaTau_quarterK_mul_div]
  simp only [jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ite_false, quarterK, compEllIntKTau]
  field_simp

/-- DLMF 23.6.24: `℘(z + ω₁) - e₁ = (Kk'/ω₁)² sc²(Kz/ω₁, k)`, `z + ω₁ ∉ 𝕃`. -/
@[dlmf 23.6.E24]
theorem weierstrassP_add_ω₁_sub_e_one_eq_sc {z : ℂ} (hz : z + H.ω₁ ∉ H.lattice) :
    H.weierstrassP (z + H.ω₁) - H.e 1 =
      (H.quarterK * H.comodulus / H.ω₁) ^ 2 * jacobiScTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hθ := H.jacobiThetaOneTau_pi_mul_div_ne_zero hz
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  have hw : π * (z + H.ω₁) / (2 * H.ω₁) = π * z / (2 * H.ω₁) + π / 2 := by field_simp
  rw [hw] at hθ
  have a : jacobiThetaTwoTau (π * z / (2 * H.ω₁) + π / 2) H.tau =
      -jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau := by
    rw [(jacobiThetaTwoTau_half_periods _ _).1, add_assoc, add_halves, jacobiThetaOneTau_add_pi]
  rw [(jacobiThetaOneTau_add_sub_half_pi _ _).1] at hθ
  rw [H.weierstrassP_sub_e_one_eq_jacobiTheta_sq hz, hw, a, (jacobiThetaOneTau_add_sub_half_pi _ _).1, jacobiScTau, jacobiPQTau,
    H.jacobiZetaTau_quarterK_mul_div]
  simp only [jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ite_false, quarterK, compEllIntKTau,
    comodulus, jacobiComodulusTau]
  field_simp

/-- DLMF 23.6.25: `℘(z + ω₂) - e₂ = -(Kkk'/ω₁)² sd²(Kz/ω₁, k)`, `z + ω₂ ∉ 𝕃`. -/
@[dlmf 23.6.E25]
theorem weierstrassP_add_ω₂_sub_e_two_eq_sd {z : ℂ} (hz : z + H.ω₂ ∉ H.lattice) :
    H.weierstrassP (z + H.ω₂) - H.e 2 =
      -(H.quarterK * H.modulus * H.comodulus / H.ω₁) ^ 2 *
        jacobiSdTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hθ := H.jacobiThetaOneTau_pi_mul_div_ne_zero hz
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  set c : ℂ := π / 2 + π * H.tau / 2 with hc
  have hw : π * (z + H.ω₂) / (2 * H.ω₁) = π * z / (2 * H.ω₁) - c := by
    rw [hc, HalfPeriods.tau, HalfPeriods.ω₂]; field_simp; ring
  rw [hw] at hθ
  have a := (jacobiThetaThreeTau_half_periods ((π * z / (2 * H.ω₁)) - c) H.tau).2.2
  have b := (jacobiThetaOneTau_half_periods ((π * z / (2 * H.ω₁)) - c) H.tau).2.2
  rw [show (π * z / (2 * H.ω₁)) - c + π / 2 + π * H.tau / 2 = (π * z / (2 * H.ω₁)) by
    rw [hc]; ring] at a b
  have hM : thetaMultiplierM ((π * z / (2 * H.ω₁)) - c) H.tau ≠ 0 := exp_ne_zero _
  have hθ3 : jacobiThetaThreeTau (π * z / (2 * H.ω₁)) H.tau ≠ 0 := by
    intro h0; rw [h0, mul_zero] at b; exact hθ b
  rw [H.weierstrassP_sub_e_two_eq_jacobiTheta_sq hz, hw, jacobiSdTau, jacobiPQTau, H.jacobiZetaTau_quarterK_mul_div]
  simp only [jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ite_false, quarterK, compEllIntKTau,
    modulus, jacobiModulusTau, comodulus, jacobiComodulusTau]
  rw [a, b]
  generalize thetaMultiplierM (π * z / (2 * H.ω₁) - c) H.tau = M at *
  generalize jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau = T1 at *
  generalize jacobiThetaThreeTau (π * z / (2 * H.ω₁)) H.tau = T3 at *
  field_simp
  rw [show (I : ℂ) ^ 2 = -1 from I_sq]
  ring

/-- DLMF 23.6.26: `℘(z + ω₃) - e₃ = (Kk/ω₁)² sn²(Kz/ω₁, k)`, `z + ω₃ ∉ 𝕃`. -/
@[dlmf 23.6.E26]
theorem weierstrassP_add_ω₃_sub_e_three_eq_sn {z : ℂ} (hz : z + H.ω₃ ∉ H.lattice) :
    H.weierstrassP (z + H.ω₃) - H.e 3 =
      (H.quarterK * H.modulus / H.ω₁) ^ 2 * jacobiSnTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hθ := H.jacobiThetaOneTau_pi_mul_div_ne_zero hz
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  have hw : π * (z + H.ω₃) / (2 * H.ω₁) = π * z / (2 * H.ω₁) + π * H.tau / 2 := by
    rw [HalfPeriods.tau]; field_simp
  rw [hw] at hθ
  set w := π * z / (2 * H.ω₁)
  have a := (jacobiThetaOneTau_half_periods w H.tau).2.1
  have b := (jacobiThetaFourTau_half_periods w H.tau).2.1
  have hM : thetaMultiplierM w H.tau ≠ 0 := exp_ne_zero _
  rw [H.weierstrassP_sub_e_three_eq_jacobiTheta_sq hz, hw, jacobiSnTau, jacobiPQTau, H.jacobiZetaTau_quarterK_mul_div]
  simp only [jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ite_false, quarterK, compEllIntKTau,
    modulus, jacobiModulusTau]
  rw [a, b]
  field_simp

end HalfPeriods

/-- Points off a period lattice: every point has a punctured neighbourhood avoiding `𝕃`. -/
private lemma eventually_notMem_lattice (L : PeriodPair) (a : ℂ) :
    ∀ᶠ w in 𝓝[≠] a, w ∉ L.lattice := by
  have hU : IsOpen ((L.lattice : Set ℂ) \ {a})ᶜ := L.isOpen_compl_lattice_sdiff
  have ha : a ∈ ((L.lattice : Set ℂ) \ {a})ᶜ := by simp
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds ha), self_mem_nhdsWithin] with w hw hwa
  intro hwL; exact hw ⟨hwL, hwa⟩

/-- `ζ` is meromorphic. -/
private lemma meromorphicAt_weierstrassZeta (L : PeriodPair) (a : ℂ) :
    MeromorphicAt (weierstrassZeta L) a := by
  by_cases ha : a ∈ L.lattice
  · have h := (analyticAt_weierstrassZeta_sub L ha).meromorphicAt.add
      ((MeromorphicAt.id a).sub (MeromorphicAt.const a a)).inv
    convert h using 1; funext z; simp
  · exact (analyticOnNhd_weierstrassZeta L a ha).meromorphicAt

/-- Liouville identification: an odd elliptic function `f` for `𝕃` with `f(z + s) = -f(z)`
(`2s ∈ 𝕃`, `s ∉ 𝕃`), poles only on `𝕃 ∪ (𝕃 - s)` and `f(z) - 1/z` regular at `0` equals
`ζ(z) - ζ(z + s) + ζ(s)`. -/
private lemma weierstrassZeta_sub_add_eq_of_antiperiodic (L : PeriodPair) {s : ℂ}
    (hs : s ∉ L.lattice)
    (h2s : 2 * s ∈ L.lattice) {f : ℂ → ℂ} (hfm : ∀ z, MeromorphicAt f z)
    (hper : ∀ z, ∀ l ∈ L.lattice, f (z + l) = f z) (hanti : ∀ z, f (z + s) = -f z)
    (hodd : ∀ z, f (-z) = -f z)
    (han : ∀ z, z ∉ L.lattice → z + s ∉ L.lattice → AnalyticAt ℂ f z)
    (h0 : ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ (fun z => f z - 1 / z) =ᶠ[𝓝[≠] 0] A)
    {z : ℂ} (hz : z ∉ L.lattice) (hz' : z + s ∉ L.lattice) :
    weierstrassZeta L z - weierstrassZeta L (z + s) + weierstrassZeta L s = f z := by
  classical
  set ζ := weierstrassZeta L with hζ
  set P : ℂ → Prop := fun w => w ∈ L.lattice ∨ w + s ∈ L.lattice with hP
  set F : ℂ → ℂ := fun w => ζ w - ζ (w + s) + ζ s with hF
  set G : ℂ → ℂ := fun w => if P w then 0 else F w - f w with hG
  have hmem_add : ∀ {w l : ℂ}, l ∈ L.lattice → (w + l ∈ L.lattice ↔ w ∈ L.lattice) := by
    intro w l hl
    exact ⟨fun h => by simpa using L.lattice.sub_mem h hl, fun h => L.lattice.add_mem h hl⟩
  have hPl : ∀ w, ∀ l ∈ L.lattice, (P (w + l) ↔ P w) := by
    intro w l hl
    simp only [hP, hmem_add hl, show w + l + s = w + s + l by ring]
  have hPs : ∀ w, (P (w + s) ↔ P w) := by
    intro w
    simp only [hP, show w + s + s = w + 2 * s by ring, hmem_add h2s]; tauto
  have hPneg : ∀ w, (P (-w) ↔ P w) := by
    intro w
    have e1 : -w ∈ L.lattice ↔ w ∈ L.lattice := neg_mem_iff
    have e2 : -w + s ∈ L.lattice ↔ w + s ∈ L.lattice := by
      rw [show -w + s = -(w + s) + 2 * s by ring, hmem_add h2s, neg_mem_iff]
    simp only [hP, e1, e2]
  -- quasi-periodicity of `ζ`
  have hns : -s ∉ L.lattice := fun h => hs (by simpa using L.lattice.neg_mem h)
  have hζ2s : ∀ w, w ∉ L.lattice → ζ (w + 2 * s) = ζ w + 2 * ζ s := by
    intro w hw
    have := weierstrassZeta_add_sub_eq_of_mem L h2s hw hns
    rw [show -s + 2 * s = s by ring, weierstrassZeta_neg] at this
    simp only [hζ]; linear_combination this
  have hFl : ∀ w, ¬ P w → ∀ l ∈ L.lattice, F (w + l) = F w := by
    intro w hw l hl
    simp only [hP, not_or] at hw
    have := weierstrassZeta_add_sub_eq_of_mem L hl hw.1 hw.2
    simp only [hF, show w + l + s = w + s + l by ring]
    linear_combination this
  have hFs : ∀ w, ¬ P w → F (w + s) = -F w := by
    intro w hw
    simp only [hP, not_or] at hw
    simp only [hF, show w + s + s = w + 2 * s by ring, hζ2s w hw.1]; ring
  have hFneg : ∀ w, ¬ P w → F (-w) = -F w := by
    intro w hw
    simp only [hP, not_or] at hw
    have hw' : -w - s ∉ L.lattice := fun h => hw.2 (by
      simpa [show -(-w - s) = w + s by ring] using L.lattice.neg_mem h)
    have e1 : ζ (-w + s) = -ζ (w + s) + 2 * ζ s := by
      rw [show -w + s = (-w - s) + 2 * s by ring, hζ2s _ hw', show -w - s = -(w + s) by ring]
      simp only [hζ, weierstrassZeta_neg]
    have e2 : ζ (-w) = -ζ w := by simp only [hζ, weierstrassZeta_neg]
    simp only [hF]
    rw [e1, e2]; ring
  have hGl : ∀ w, ∀ l ∈ L.lattice, G (w + l) = G w := by
    intro w l hl
    by_cases hw : P w
    · simp [hG, hw, (hPl w l hl).mpr hw]
    · simp only [hG, hw, (hPl w l hl).not.mpr hw, ite_false, hFl w hw l hl, hper w l hl]
  have hGs : ∀ w, G (w + s) = -G w := by
    intro w
    by_cases hw : P w
    · simp [hG, hw, (hPs w).mpr hw]
    · simp only [hG, hw, (hPs w).not.mpr hw, ite_false, hFs w hw, hanti]; ring
  have hGneg : ∀ w, G (-w) = -G w := by
    intro w
    by_cases hw : P w
    · simp [hG, hw, (hPneg w).mpr hw]
    · simp only [hG, hw, (hPneg w).not.mpr hw, ite_false, hFneg w hw, hodd]; ring
  -- local structure
  have hPev : ∀ a, ∀ᶠ w in 𝓝[≠] a, ¬ P w := by
    intro a
    have h1 := eventually_notMem_lattice L a
    have h2 : ∀ᶠ w in 𝓝[≠] a, w + s ∉ L.lattice := by
      have ht : Tendsto (fun w => w + s) (𝓝[≠] a) (𝓝[≠] (a + s)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          ((continuous_id.add continuous_const).tendsto a |>.mono_left nhdsWithin_le_nhds)
          (by filter_upwards [self_mem_nhdsWithin] with w hw
              exact fun h => hw (add_right_cancel h))
      exact ht.eventually (eventually_notMem_lattice L (a + s))
    filter_upwards [h1, h2] with w hw1 hw2
    simp only [hP, not_or]; exact ⟨hw1, hw2⟩
  have hGev : ∀ a, G =ᶠ[𝓝[≠] a] fun w => F w - f w := by
    intro a
    filter_upwards [hPev a] with w hw
    simp [hG, hw]
  have hFm : ∀ a, MeromorphicAt F a := by
    intro a
    have e : F = (weierstrassZeta L - weierstrassZeta L ∘ fun w => w + s) + fun _ => ζ s := by
      funext w; simp [hF, hζ]
    rw [e]
    exact ((meromorphicAt_weierstrassZeta L a).sub
      ((meromorphicAt_weierstrassZeta L (a + s)).comp_analyticAt (g := fun w : ℂ => w + s)
        (by fun_prop))).add (MeromorphicAt.const _ a)
  have hGm : Meromorphic G := fun a =>
    ((hFm a).sub (hfm a)).congr (hGev a).symm
  have hGan : ∀ a, ¬ P a → AnalyticAt ℂ G a := by
    intro a ha
    simp only [hP, not_or] at ha
    have hopen : IsOpen {w : ℂ | ¬ P w} := by
      have h1 : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
      have h2 : IsOpen ((fun w => w + s) ⁻¹' (L.latticeᶜ : Set ℂ)) :=
        h1.preimage (continuous_id.add continuous_const)
      convert h1.inter h2 using 1
      ext w; simp [hP]
    have hFa : AnalyticAt ℂ F a := by
      have h1 := analyticOnNhd_weierstrassZeta L a ha.1
      have h2 := (analyticOnNhd_weierstrassZeta L (a + s) ha.2).comp_of_eq
        (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w + s) a) rfl
      exact (h1.sub h2).add analyticAt_const
    refine (hFa.sub (han a ha.1 ha.2)).congr ?_
    filter_upwards [hopen.mem_nhds (show ¬ P a by simp [hP, ha.1, ha.2])] with w hw
    simp [hG, hw]
  -- orders
  have hord0 : 0 ≤ meromorphicOrderAt G 0 := by
    obtain ⟨A, hA, hfA⟩ := h0
    have h1 := analyticAt_weierstrassZeta_sub L L.lattice.zero_mem
    have h2 := (analyticOnNhd_weierstrassZeta L (0 + s) (by simpa using hs)).comp_of_eq
        (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w + s) 0) rfl
    have hev : G =ᶠ[𝓝[≠] 0] fun w => (ζ w - 1 / (w - 0)) - ζ (w + s) + ζ s - A w := by
      filter_upwards [hGev 0, hfA] with w hw hwA
      rw [hw, ← hwA]; simp only [hF, sub_zero]; ring
    rw [meromorphicOrderAt_congr hev]
    exact (((h1.sub h2).add analyticAt_const).sub hA).meromorphicOrderAt_nonneg
  have hord : ∀ x, 0 ≤ meromorphicOrderAt G x := by
    intro x
    by_cases hx : P x
    · rcases hx with hx | hx
      · have e : G ∘ (· + x) = G := funext fun w => hGl w x hx
        have h1 := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (x := (0 : ℂ))
          (c := x) (f := G)
        rw [zero_add, e] at h1
        rw [← h1]; exact hord0
      · have e : G ∘ (· + x) = (-1 : ℂ) • G := by
          funext w
          have h1 := hGs (w + x)
          rw [show w + x + s = w + (x + s) by ring, hGl w _ hx] at h1
          simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
          linear_combination h1
        have h1 := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (x := (0 : ℂ))
          (c := x) (f := G)
        rw [zero_add, e, meromorphicOrderAt_const_smul_eq_meromorphicOrderAt
          (by norm_num)] at h1
        rw [← h1]; exact hord0
    · exact (hGan x hx).meromorphicOrderAt_nonneg
  obtain ⟨c, hc⟩ := exists_eq_const_of_periodic_of_order_nonneg L hGm hGl hord
  have hhalf : ¬ P (s / 2) := by
    have hh : s / 2 ∉ L.lattice := by
      intro h
      have := L.lattice.add_mem h h
      rw [show s / 2 + s / 2 = s by ring] at this
      exact hs this
    simp only [hP, not_or]
    refine ⟨hh, fun h => hh ?_⟩
    have := L.lattice.sub_mem h2s h
    rwa [show 2 * s - (s / 2 + s) = s / 2 by ring] at this
  have hhalf' : ¬ P (-(s / 2)) := (hPneg _).not.mpr hhalf
  have hc0 : c = 0 := by
    have e1 := hc _ (hGan _ hhalf)
    have e2 := hc _ (hGan _ hhalf')
    rw [hGneg, e1] at e2
    linear_combination -e2 / 2
  have hzP : ¬ P z := by simp [hP, hz, hz']
  have := hc z (hGan z hzP)
  rw [hc0] at this
  simp only [hG, hzP, ite_false, hF] at this
  exact sub_eq_zero.mp this

/-- Linear independence of the generators of a period lattice, with real coefficients. -/
private lemma eq_zero_of_real_combination (L : PeriodPair) {a b : ℝ}
    (h : (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ = 0) : a = 0 ∧ b = 0 := by
  have := LinearIndependent.pair_iff.mp L.indep a b (by simpa [Complex.real_smul] using h)
  exact this

/-- A function periodic under both generators is periodic under the lattice. -/
private lemma periodic_lattice_of_generators (L : PeriodPair) {f : ℂ → ℂ}
    (h1 : ∀ z, f (z + L.ω₁) = f z) (h2 : ∀ z, f (z + L.ω₂) = f z) :
    ∀ z, ∀ l ∈ L.lattice, f (z + l) = f z := by
  intro z l hl
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hl
  have p1 : Function.Periodic f L.ω₁ := h1
  have p2 : Function.Periodic f L.ω₂ := h2
  rw [← add_assoc, (p2.int_mul n) (z + m * L.ω₁), (p1.int_mul m) z]

open DLMF.JacobiElliptic in
/-- The Liouville identification specialized to `ps(z, k)`, `p ≠ s`. -/
private lemma weierstrassZeta_sub_add_eq_jacobiPQk_s {k : ℂ} (hk : k ∈ jacobiModulusDomain)
    {p : JacobiLetter} (hp : p ≠ .s) (L : PeriodPair) {s : ℂ} (hs : s ∉ L.lattice)
    (h2s : 2 * s ∈ L.lattice)
    (h1 : ∀ z, jacobiPQk p .s (z + L.ω₁) k = jacobiPQk p .s z k)
    (h2 : ∀ z, jacobiPQk p .s (z + L.ω₂) k = jacobiPQk p .s z k)
    (hanti : ∀ z, jacobiPQk p .s (z + s) k = -jacobiPQk p .s z k)
    (hcong : ∀ z ∈ jacobiCongruentk 0 k, z ∈ L.lattice ∨ z + s ∈ L.lattice)
    {z : ℂ} (hz : z ∉ L.lattice) (hz' : z + s ∉ L.lattice) :
    weierstrassZeta L z - weierstrassZeta L (z + s) + weierstrassZeta L s =
      jacobiPQk p .s z k :=
  weierstrassZeta_sub_add_eq_of_antiperiodic L hs h2s (f := fun w => jacobiPQk p .s w k)
    (fun w => (poleDichotomy_jacobiPQk hk hp).meromorphicAt w)
    (periodic_lattice_of_generators L (f := fun w => jacobiPQk p .s w k) h1 h2) hanti
    (fun w => by rw [jacobiPQk_neg]; simp [hp])
    (fun w hw hw' => analyticAt_jacobiPQk_s hk hp fun h => (hcong w h).elim hw hw')
    (exists_analyticAt_jacobiPQk_s_sub_one_div hk hp) hz hz'

/-- DLMF 23.6.27: for a modulus `k` (`ℜk > 0`, `k ∉ [1, ∞)`), `K = K(k)`, `K' = K(k')` and
`𝕃₁` the lattice with generators `4K, 2iK'`,
`ζ(z|𝕃₁) - ζ(z + 2K|𝕃₁) + ζ(2K|𝕃₁) = ns(z, k)` for `z, z + 2K ∉ 𝕃₁`. -/
@[dlmf 23.6.E27]
theorem weierstrassZeta_ns {k : ℂ} (hk : k ∈ jacobiModulusDomain) (L : PeriodPair)
    (h₁ : L.ω₁ = 4 * compEllIntKk k) (h₂ : L.ω₂ = 2 * I * compEllIntKpk k) {z : ℂ}
    (hz : z ∉ L.lattice) (hz' : z + 2 * compEllIntKk k ∉ L.lattice) :
    weierstrassZeta L z - weierstrassZeta L (z + 2 * compEllIntKk k) +
      weierstrassZeta L (2 * compEllIntKk k) = jacobiNsk z k := by
  refine weierstrassZeta_sub_add_eq_jacobiPQk_s hk (p := .n) (by decide) L ?_ ?_ ?_ ?_
    (fun w => (jacobiNsk_shift hk w).2.2.2.1) ?_ hz hz'
  · intro h
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp h
    have h0 : (((m : ℝ) - 1 / 2 : ℝ) : ℂ) * L.ω₁ + ((n : ℝ) : ℂ) * L.ω₂ = 0 := by
      rw [h₁, h₂] at hmn ⊢; push_cast; linear_combination hmn
    have := (eq_zero_of_real_combination L h0).1
    have h2 : (2 * m : ℝ) = 1 := by linarith
    have : (2 * m : ℤ) = 1 := by exact_mod_cast h2
    omega
  · exact PeriodPair.mem_lattice.mpr ⟨1, 0, by rw [h₁]; push_cast; ring⟩
  · intro w
    change jacobiNsk (w + L.ω₁) k = jacobiNsk w k
    rw [h₁, show w + 4 * compEllIntKk k = w + 2 * compEllIntKk k + 2 * compEllIntKk k by ring,
      (jacobiNsk_shift hk _).2.2.2.1, (jacobiNsk_shift hk w).2.2.2.1, neg_neg]
  · intro w
    rw [h₂, show 2 * I * compEllIntKpk k = 2 * (I * compEllIntKpk k) by ring]
    exact (jacobiNsk_shift hk w).2.2.2.2.2
  · rintro w ⟨m, n, rfl⟩
    rcases Int.even_or_odd' m with ⟨a, rfl | rfl⟩
    · left; exact PeriodPair.mem_lattice.mpr ⟨a, n, by rw [h₁, h₂]; push_cast; ring⟩
    · right; exact PeriodPair.mem_lattice.mpr ⟨a + 1, n, by rw [h₁, h₂]; push_cast; ring⟩

/-- DLMF 23.6.28: with `𝕃₂` generated by `2K - 2iK'`, `2K + 2iK'`,
`ζ(z|𝕃₂) - ζ(z + 2K|𝕃₂) + ζ(2K|𝕃₂) = ds(z, k)` for `z, z + 2K ∉ 𝕃₂`. -/
@[dlmf 23.6.E28]
theorem weierstrassZeta_ds {k : ℂ} (hk : k ∈ jacobiModulusDomain) (L : PeriodPair)
    (h₁ : L.ω₁ = 2 * compEllIntKk k - 2 * I * compEllIntKpk k)
    (h₂ : L.ω₂ = 2 * compEllIntKk k + 2 * I * compEllIntKpk k) {z : ℂ}
    (hz : z ∉ L.lattice) (hz' : z + 2 * compEllIntKk k ∉ L.lattice) :
    weierstrassZeta L z - weierstrassZeta L (z + 2 * compEllIntKk k) +
      weierstrassZeta L (2 * compEllIntKk k) = jacobiDsk z k := by
  refine weierstrassZeta_sub_add_eq_jacobiPQk_s hk (p := .d) (by decide) L ?_ ?_ ?_ ?_
    (fun w => (jacobiDsk_shift hk w).2.2.2.1) ?_ hz hz'
  · intro h
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp h
    have h0 : (((m : ℝ) - 1 / 2 : ℝ) : ℂ) * L.ω₁ + (((n : ℝ) - 1 / 2 : ℝ) : ℂ) * L.ω₂ = 0 := by
      rw [h₁, h₂] at hmn ⊢; push_cast; linear_combination hmn
    have := (eq_zero_of_real_combination L h0).1
    have h2 : (2 * m : ℝ) = 1 := by linarith
    have : (2 * m : ℤ) = 1 := by exact_mod_cast h2
    omega
  · exact PeriodPair.mem_lattice.mpr ⟨1, 1, by rw [h₁, h₂]; push_cast; ring⟩
  · intro w
    change jacobiDsk (w + L.ω₁) k = jacobiDsk w k
    have e := (jacobiDsk_shift hk (w - 2 * (I * compEllIntKpk k))).2.2.2.2.2
    rw [sub_add_cancel] at e
    rw [h₁, show w + (2 * compEllIntKk k - 2 * I * compEllIntKpk k) =
      (w - 2 * (I * compEllIntKpk k)) + 2 * compEllIntKk k by ring,
      (jacobiDsk_shift hk _).2.2.2.1, e]
  · intro w
    rw [h₂, show w + (2 * compEllIntKk k + 2 * I * compEllIntKpk k) =
      w + 2 * compEllIntKk k + 2 * (I * compEllIntKpk k) by ring]
    exact (jacobiDsk_shift hk w).2.2.2.2.1
  · rintro w ⟨m, n, rfl⟩
    rcases Int.even_or_odd' (m + n) with ⟨c, hc | hc⟩
    · left
      exact PeriodPair.mem_lattice.mpr ⟨m - c, c, by
        rw [h₁, h₂]; have : (n : ℂ) = 2 * c - m := by
          rw [show (n : ℂ) = ((n : ℤ) : ℂ) from rfl]; push_cast [show n = 2 * c - m by omega]
          ring
        rw [this]; push_cast; ring⟩
    · right
      exact PeriodPair.mem_lattice.mpr ⟨m - c, c + 1, by
        rw [h₁, h₂]; have : (n : ℂ) = 2 * c + 1 - m := by
          push_cast [show n = 2 * c + 1 - m by omega]; ring
        rw [this]; push_cast; ring⟩

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
  have hanti : ∀ w, jacobiCsk (w + 2 * I * compEllIntKpk k) k = -jacobiCsk w k := by
    intro w
    rw [show w + 2 * I * compEllIntKpk k = w + 2 * (I * compEllIntKpk k) by ring]
    exact (jacobiCsk_shift hk w).2.2.2.2.2
  refine weierstrassZeta_sub_add_eq_jacobiPQk_s hk (p := .c) (by decide) L ?_ ?_ ?_ ?_
    hanti ?_ hz hz'
  · intro h
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp h
    have h0 : ((m : ℝ) : ℂ) * L.ω₁ + (((n : ℝ) - 1 / 2 : ℝ) : ℂ) * L.ω₂ = 0 := by
      rw [h₁, h₂] at hmn ⊢; push_cast; linear_combination hmn
    have := (eq_zero_of_real_combination L h0).2
    have h2 : (2 * n : ℝ) = 1 := by linarith
    have : (2 * n : ℤ) = 1 := by exact_mod_cast h2
    omega
  · exact PeriodPair.mem_lattice.mpr ⟨0, 1, by rw [h₂]; push_cast; ring⟩
  · intro w
    rw [h₁]; exact (jacobiCsk_shift hk w).2.2.2.1
  · intro w
    change jacobiCsk (w + L.ω₂) k = jacobiCsk w k
    rw [h₂, show w + 4 * I * compEllIntKpk k =
      w + 2 * I * compEllIntKpk k + 2 * I * compEllIntKpk k by ring, hanti, hanti, neg_neg]
  · rintro w ⟨m, n, rfl⟩
    rcases Int.even_or_odd' n with ⟨a, rfl | rfl⟩
    · left; exact PeriodPair.mem_lattice.mpr ⟨m, a, by rw [h₁, h₂]; push_cast; ring⟩
    · right; exact PeriodPair.mem_lattice.mpr ⟨m, a + 1, by rw [h₁, h₂]; push_cast; ring⟩

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

end
end
