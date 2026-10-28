/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Relations.ThetaIdentities

/-!
# Relations between Weierstrass and Jacobian elliptic functions

The theta representations specialize to Jacobian elliptic functions. Principal-modulus and
lattice-quarter-period forms retain their respective domain assumptions.

Source references and common attribution are retained in
`DLMF.Weierstrass.Relations`.
-/

@[expose] public section

open Complex PeriodPair DLMF.Elliptic DLMF.Theta DLMF.JacobiElliptic MeasureTheory

open scoped Real

open Filter Topology

noncomputable section

namespace DLMF.Weierstrass

namespace HalfPeriods

variable (H : HalfPeriods)

/-- DLMF 23.6.13: with `z = πu/(2ω₁)`, `ζ(u) = η₁u/ω₁ + (π/(2ω₁)) d/dz ln θ₁(z,q)`,
`u ∉ 𝕃`. -/
@[dlmf 23.6.E13]
theorem weierstrassZeta_eq_theta {u : ℂ} (hu : u ∉ H.lattice) :
    H.weierstrassZeta u = H.eta 1 / H.ω₁ * u + π / (2 * H.ω₁) *
      (deriv (fun z ↦ jacobiThetaOneTau z H.tau) (π * u / (2 * H.ω₁)) /
        jacobiThetaOneTau (π * u / (2 * H.ω₁)) H.tau) := by
  exact H.p23R1_zeta_theta hu

/-- DLMF 23.6.14: with `z = πu/(2ω₁)`,
`℘(u) = (π/(2ω₁))² (θ₁'''(0,q)/(3θ₁'(0,q)) - d²/dz² ln θ₁(z,q))`, `u ∉ 𝕃`. -/
@[dlmf 23.6.E14]
theorem weierstrassP_eq_theta {u : ℂ} (hu : u ∉ H.lattice) :
    H.weierstrassP u = (π / (2 * H.ω₁)) ^ 2 *
      (thetaOneTripleDerivNull H.tau / (3 * jacobiThetaOneDerivNullTau H.tau) -
        deriv (fun z ↦ deriv (fun w ↦ jacobiThetaOneTau w H.tau) z / jacobiThetaOneTau z H.tau)
          (π * u / (2 * H.ω₁))) := by
  have hω := H.ω₁_ne_zero
  have hD := H.p23R1_thetaOneDeriv_ne_zero
  rw [H.p23R1_wp_theta_aux hu, H.p23R1_eta_one_theta]
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
  have hD := H.p23R1_thetaOneDeriv_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  have hL := H.p23R1_sigma_theta.2
  have hsum := H.eta_one_add_eta_two_add_eta_three
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  set w := π * u / (2 * H.ω₁) with hw
  rcases hj with rfl | rfl | rfl
  · rw [H.p23R1_sigma_theta.1, H.p23R1_sigma_theta.1, p23R1_thetaSigma, p23R1_thetaSigma,
      halfPeriod_one,
      show π * (u + H.ω₁) / (2 * H.ω₁) = w + π / 2 by rw [hw]; field_simp,
      show π * H.ω₁ / (2 * H.ω₁) = 0 + π / 2 by rw [zero_add]; field_simp,
      (p23R1_theta_shift_one _ _).1, (p23R1_theta_shift_one _ _).1]
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
    rw [H.p23R1_sigma_theta.1, H.p23R1_sigma_theta.1, p23R1_thetaSigma, p23R1_thetaSigma,
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
    rw [H.p23R1_sigma_theta.1, H.p23R1_sigma_theta.1, p23R1_thetaSigma, p23R1_thetaSigma,
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
  obtain ⟨d3, d2⟩ := H.p23R1_e_diff
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
  obtain ⟨d3, -⟩ := H.p23R1_e_diff
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
    exact mul_ne_zero (by simp [Real.pi_ne_zero]) (pow_ne_zero _ (je22a_thetaThree_zero_ne_zero H.tau_im_pos))
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
lemma p23R1_zeta_arg (z : ℂ) :
    jacobiZetaTau (H.quarterK * z / H.ω₁) H.tau = π * z / (2 * H.ω₁) := by
  have hω := H.ω₁_ne_zero
  have n3 := (jacobiThetaNullTau_ne_zero H.tau_im_pos).2.1
  simp only [jacobiThetaThreeNullTau] at n3
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [jacobiZetaTau, quarterK, compEllIntKTau]
  field_simp

/-- `θ₁(w) ≠ 0` at `w = πz/(2ω₁)` for `z ∉ 𝕃`. -/
theorem p23R1_thetaOne_ne_zero {z : ℂ} (hz : z ∉ H.lattice) :
    jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau ≠ 0 := by
  intro h0; apply hz; apply (H.p23R1_thetaSigma_eq_zero_iff z).mp
  simp only [p23R1_thetaSigma, h0, mul_zero, zero_div]

/-- DLMF 23.6.21: `℘(z) - e₁ = (K²/ω₁²) cs²(Kz/ω₁, k)`, `z ∉ 𝕃`. -/
@[dlmf 23.6.E21]
theorem weierstrassP_sub_e_one_eq_cs {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 1 =
      H.quarterK ^ 2 / H.ω₁ ^ 2 * jacobiCsTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hθ := H.p23R1_thetaOne_ne_zero hz
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  rw [H.p23R1_wp_sub_e_one hz, jacobiCsTau, jacobiPQTau, H.p23R1_zeta_arg]
  simp only [jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ite_false, quarterK, compEllIntKTau]
  field_simp

/-- DLMF 23.6.22: `℘(z) - e₂ = (K²/ω₁²) ds²(Kz/ω₁, k)`, `z ∉ 𝕃`. -/
@[dlmf 23.6.E22]
theorem weierstrassP_sub_e_two_eq_ds {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 2 =
      H.quarterK ^ 2 / H.ω₁ ^ 2 * jacobiDsTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hθ := H.p23R1_thetaOne_ne_zero hz
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  rw [H.p23R1_wp_sub_e_two hz, jacobiDsTau, jacobiPQTau, H.p23R1_zeta_arg]
  simp only [jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ite_false, quarterK, compEllIntKTau]
  field_simp

/-- DLMF 23.6.23: `℘(z) - e₃ = (K²/ω₁²) ns²(Kz/ω₁, k)`, `z ∉ 𝕃`. -/
@[dlmf 23.6.E23]
theorem weierstrassP_sub_e_three_eq_ns {z : ℂ} (hz : z ∉ H.lattice) :
    H.weierstrassP z - H.e 3 =
      H.quarterK ^ 2 / H.ω₁ ^ 2 * jacobiNsTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hθ := H.p23R1_thetaOne_ne_zero hz
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  rw [H.p23R1_wp_sub_e_three hz, jacobiNsTau, jacobiPQTau, H.p23R1_zeta_arg]
  simp only [jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ite_false, quarterK, compEllIntKTau]
  field_simp

/-- DLMF 23.6.24: `℘(z + ω₁) - e₁ = (Kk'/ω₁)² sc²(Kz/ω₁, k)`, `z + ω₁ ∉ 𝕃`. -/
@[dlmf 23.6.E24]
theorem weierstrassP_add_ω₁_sub_e_one_eq_sc {z : ℂ} (hz : z + H.ω₁ ∉ H.lattice) :
    H.weierstrassP (z + H.ω₁) - H.e 1 =
      (H.quarterK * H.comodulus / H.ω₁) ^ 2 * jacobiScTau (H.quarterK * z / H.ω₁) H.tau ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hθ := H.p23R1_thetaOne_ne_zero hz
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  have hw : π * (z + H.ω₁) / (2 * H.ω₁) = π * z / (2 * H.ω₁) + π / 2 := by field_simp
  rw [hw] at hθ
  have a : jacobiThetaTwoTau (π * z / (2 * H.ω₁) + π / 2) H.tau =
      -jacobiThetaOneTau (π * z / (2 * H.ω₁)) H.tau := by
    rw [(jacobiThetaTwoTau_half_periods _ _).1, add_assoc, add_halves, jacobiThetaOneTau_add_pi]
  rw [(p23R1_theta_shift_one _ _).1] at hθ
  rw [H.p23R1_wp_sub_e_one hz, hw, a, (p23R1_theta_shift_one _ _).1, jacobiScTau, jacobiPQTau,
    H.p23R1_zeta_arg]
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
  have hθ := H.p23R1_thetaOne_ne_zero hz
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
  rw [H.p23R1_wp_sub_e_two hz, hw, jacobiSdTau, jacobiPQTau, H.p23R1_zeta_arg]
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
  have hθ := H.p23R1_thetaOne_ne_zero hz
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  have hw : π * (z + H.ω₃) / (2 * H.ω₁) = π * z / (2 * H.ω₁) + π * H.tau / 2 := by
    rw [HalfPeriods.tau]; field_simp
  rw [hw] at hθ
  set w := π * z / (2 * H.ω₁)
  have a := (jacobiThetaOneTau_half_periods w H.tau).2.1
  have b := (jacobiThetaFourTau_half_periods w H.tau).2.1
  have hM : thetaMultiplierM w H.tau ≠ 0 := exp_ne_zero _
  rw [H.p23R1_wp_sub_e_three hz, hw, jacobiSnTau, jacobiPQTau, H.p23R1_zeta_arg]
  simp only [jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ite_false, quarterK, compEllIntKTau,
    modulus, jacobiModulusTau]
  rw [a, b]
  field_simp

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

end
end
