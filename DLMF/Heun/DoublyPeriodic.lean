/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMF.Heun.LocalSolutions
public import DLMF.JacobiElliptic.SpecialValues
public import DLMF.JacobiElliptic.AnalyticProperties
public import DLMF.Weierstrass.EllipticFunctionsAndInvariants
public import DLMF.Weierstrass.Relations

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

/-- `sn(z, k) ≠ 0` forces `z` to be a regular point (`θ₄ ≠ 0`): at a pole the totalized
quotient is `0`. -/
lemma p1h_regular_of_jacobiSnk_ne_zero {k z : ℂ} (h : jacobiSnk z k ≠ 0) :
    jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
  intro h0
  apply h
  simp [jacobiSnk, jacobiPQk, jacobiGlaisher, h0]

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
  have hk0 : k ≠ 0 := fun h => by rw [h] at hk; exact lt_irrefl _ hk.1
  refine p1h_isLinearODE2On_comp
    (φ₁ := fun ζ => 2 * (jacobiSnk ζ k * jacobiCnk ζ k * jacobiDnk ζ k))
    (φ₂ := fun ζ => 2 * (jacobiCnk ζ k ^ 2 * jacobiDnk ζ k ^ 2 -
      jacobiSnk ζ k ^ 2 * jacobiDnk ζ k ^ 2 - k ^ 2 * jacobiSnk ζ k ^ 2 * jacobiCnk ζ k ^ 2))
    hV (fun ζ hζ => ?_) (fun ζ hζ => ?_) (fun ζ hζ => (hVU ζ hζ).1) (fun ζ hζ => ?_)
    (fun ζ hζ => ?_) hW
  · have hr := p1h_regular_of_jacobiSnk_ne_zero (hVU ζ hζ).2.1
    convert (hasDerivAt_jacobiSnk hk hr).pow 2 using 1
    simp; ring
  · have hr := p1h_regular_of_jacobiSnk_ne_zero (hVU ζ hζ).2.1
    convert (((hasDerivAt_jacobiSnk hk hr).mul (hasDerivAt_jacobiCnk hk hr)).mul
      (hasDerivAt_jacobiDnk hk hr)).const_mul 2 using 1
    simp only [Pi.mul_apply]; ring
  · obtain ⟨-, hs, hc, hd⟩ := hVU ζ hζ
    have hr := p1h_regular_of_jacobiSnk_ne_zero hs
    obtain ⟨e1, e2⟩ := jacobi_sq_sum hk hr
    have f1 : jacobiSnk ζ k ^ 2 - 1 = -jacobiCnk ζ k ^ 2 := by linear_combination e1
    have f2 : jacobiSnk ζ k ^ 2 - (k ^ 2)⁻¹ = -(jacobiDnk ζ k ^ 2 / k ^ 2) := by
      field_simp; linear_combination e2
    simp only [heunCoeffP, f1, f2]
    field_simp
    ring
  · obtain ⟨-, hs, hc, hd⟩ := hVU ζ hζ
    have hr := p1h_regular_of_jacobiSnk_ne_zero hs
    obtain ⟨e1, e2⟩ := jacobi_sq_sum hk hr
    have f1 : jacobiSnk ζ k ^ 2 - 1 = -jacobiCnk ζ k ^ 2 := by linear_combination e1
    have f2 : jacobiSnk ζ k ^ 2 - (k ^ 2)⁻¹ = -(jacobiDnk ζ k ^ 2 / k ^ 2) := by
      field_simp; linear_combination e2
    simp only [heunCoeffR, f1, f2]
    field_simp
    ring

/-! ### Weierstrass's form -/

/-- DLMF 23.6.26 in the modulus form: if `e₁ - e₃ = c²` and `k² = (e₂ - e₃)/(e₁ - e₃)`, then
`sn²(iK' + cξ, k) = (℘(ξ) - e₃)/(e₂ - e₃)`. -/
lemma p3w_jacobiSnk_sq_eq (H : HalfPeriods) {k : ℂ} (hk : k ∈ jacobiModulusDomain)
    (hk2 : k ^ 2 = (H.e 2 - H.e 3) / (H.e 1 - H.e 3)) {c : ℂ} (hc : c ≠ 0)
    (hc2 : c ^ 2 = H.e 1 - H.e 3) {ξ : ℂ} (hξ : ξ ∉ H.lattice) :
    jacobiSnk (I * compEllIntKpk k + ξ * c) k ^ 2 =
      (H.weierstrassP ξ - H.e 3) / (H.e 2 - H.e 3) := by
  obtain ⟨hmod, -, hKK⟩ := jacobi_inversion_k hk
  have hK : compEllIntKk k ≠ 0 := by
    rw [← hKK, compEllIntKTau]
    exact mul_ne_zero (by simp [Real.pi_ne_zero])
      (pow_ne_zero _ (je22a_thetaThree_zero_ne_zero (jacobiTauk_im_pos hk)))
  set H' : HalfPeriods := ⟨compEllIntKk k / c, I * compEllIntKpk k / c, div_ne_zero hK hc, by
    rw [div_div_div_cancel_right₀ hc]; exact jacobiTauk_im_pos hk⟩
  obtain ⟨d12, d23, d13⟩ := H.e_distinct
  have htau : H'.tau = jacobiTauk k := by
    simp only [H', HalfPeriods.tau, jacobiTauk]
    rw [div_div_div_cancel_right₀ hc]
  have hqK : H'.quarterK = compEllIntKk k := by
    rw [HalfPeriods.quarterK, htau, hKK]
  have hω1 : H'.ω₁ = compEllIntKk k / c := rfl
  have hω3 : H'.ω₃ = I * compEllIntKpk k / c := rfl
  -- the roots of `H'` agree with those of `H`
  have hm := H'.modulus_sq_eq.1
  have hq := H'.quarterK_sq_eq.1
  rw [HalfPeriods.modulus, htau, hmod, hk2] at hm
  rw [hqK, hω1] at hq
  have a13 : H'.e 1 - H'.e 3 = H.e 1 - H.e 3 := by
    rw [← hc2]; field_simp at hq; linear_combination -hq
  have a23 : H'.e 2 - H'.e 3 = H.e 2 - H.e 3 := by
    have h13' : H'.e 1 - H'.e 3 ≠ 0 := by rw [a13]; exact sub_ne_zero.mpr d13
    rw [a13] at hm
    field_simp at hm
    exact hm.symm
  have s' := H'.e_sum
  have s := H.e_sum
  have b3 : H'.e 3 = H.e 3 := by linear_combination (-(a13 + a23) + s' - s) / 3
  have b1 : H'.e 1 = H.e 1 := by linear_combination a13 + b3
  have b2 : H'.e 2 = H.e 2 := by linear_combination a23 + b3
  have hlat : H'.lattice = H.lattice := by
    refine lattice_eq_of_invariants_eq _ _ ?_ ?_
    · change H'.g₂ = H.g₂
      rw [H'.g₂_eq_e.1, H.g₂_eq_e.1, b1, b2, b3]
    · change H'.g₃ = H.g₃
      rw [H'.g₃_eq_e.1, H.g₃_eq_e.1, b1, b2, b3]
  have hwp : ∀ z, H'.weierstrassP z = H.weierstrassP z := fun z =>
    wp23_weierstrassP_eq_of_lattice_eq _ _ hlat z
  have hz : ξ + H'.ω₃ + H'.ω₃ ∉ H'.lattice := by
    rw [hlat, add_assoc, ← two_mul]
    intro h; apply hξ
    have := sub_mem h (hlat ▸ H'.two_mul_ω₃_mem)
    simpa using this
  have key := H'.weierstrassP_add_ω₃_sub_e_three_eq_sn hz
  have hper := H'.weierstrassP_add_two_mul_halfPeriod ξ (j := 3) (by simp)
  simp only [HalfPeriods.halfPeriod_three] at hper
  rw [add_assoc, ← two_mul, hper, hwp, b3, hqK, HalfPeriods.modulus, htau, hmod, hω1] at key
  have harg : compEllIntKk k * (ξ + H'.ω₃) / (compEllIntKk k / c) =
      I * compEllIntKpk k + ξ * c := by
    rw [hω3]; field_simp; ring
  rw [harg] at key
  have hsn : jacobiSnTau (I * compEllIntKpk k + ξ * c) (jacobiTauk k) =
      jacobiSnk (I * compEllIntKpk k + ξ * c) k := by
    simp only [jacobiSnTau, jacobiSnk, jacobiPQTau, jacobiPQk, jacobiZetaTau, jacobiZetak, hKK]
  rw [hsn] at key
  have h23 : H.e 2 - H.e 3 ≠ 0 := sub_ne_zero.mpr d23
  have h13 : H.e 1 - H.e 3 ≠ 0 := sub_ne_zero.mpr d13
  rw [key]
  field_simp
  rw [hk2, hc2]
  field_simp

/-- DLMF 31.2.9: with `k² = (e₂ - e₃)/(e₁ - e₃)` and `ζ = iK' + ξ(e₁ - e₃)^{1/2}`, the Jacobi
variable `z = sn²(ζ, k)` of 31.2.7 is `(℘(ξ) - e₃)/(e₂ - e₃)`; `e_j = ℘(ω_j)`,
`e₁ + e₂ + e₃ = 0`. Stated for `k` in `jacobiModulusDomain` and `ξ` off the lattice. -/
@[dlmf 31.2.E9]
theorem jacobiSnk_sq_eq_weierstrassP (H : HalfPeriods) {k : ℂ} (hk : k ∈ jacobiModulusDomain)
    (hk2 : k ^ 2 = (H.e 2 - H.e 3) / (H.e 1 - H.e 3)) {ξ : ℂ} (hξ : ξ ∉ H.lattice) :
    jacobiSnk (I * compEllIntKpk k + ξ * (H.e 1 - H.e 3) ^ (1 / 2 : ℂ)) k ^ 2 =
      (H.weierstrassP ξ - H.e 3) / (H.e 2 - H.e 3) := by
  have h13 : H.e 1 - H.e 3 ≠ 0 := sub_ne_zero.mpr H.e_distinct.2.2
  refine p3w_jacobiSnk_sq_eq H hk hk2 ?_ ?_ hξ
  · exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr h13
  · rw [one_div]; exact cpow_ofNat_inv_pow _ 2

/-- Algebra of 31.2.9–31.2.11, first-derivative coefficient. -/
lemma p3w_wf_algA {x y e₁ e₂ e₃ γ δ ε : ℂ} (hs : e₁ + e₂ + e₃ = 0)
    (h1 : x - e₁ ≠ 0) (h2 : x - e₂ ≠ 0) (h3 : x - e₃ ≠ 0) (hE : e₂ - e₃ ≠ 0)
    (hsq : y ^ 2 = 4 * (x - e₁) * (x - e₂) * (x - e₃)) :
    (6 * x ^ 2 - 2 * (e₁ ^ 2 + e₂ ^ 2 + e₃ ^ 2) / 2) / (e₂ - e₃) +
      2 * -(y * ((1 - 2 * γ) / 4 / (x - e₃) + (1 - 2 * δ) / 4 / (x - e₂) +
        (1 - 2 * ε) / 4 / (x - e₁))) * (y / (e₂ - e₃)) =
      heunCoeffP ((e₁ - e₃) / (e₂ - e₃)) γ δ ε ((x - e₃) / (e₂ - e₃)) * (y / (e₂ - e₃)) ^ 2 := by
  have hz1 : (x - e₃) / (e₂ - e₃) - 1 = (x - e₂) / (e₂ - e₃) := by field_simp; ring
  have hza : (x - e₃) / (e₂ - e₃) - (e₁ - e₃) / (e₂ - e₃) = (x - e₁) / (e₂ - e₃) := by ring
  simp only [heunCoeffP, hz1, hza]
  have he₃ : e₃ = -e₁ - e₂ := by linear_combination hs
  linear_combination (norm := skip) (-2 * ((1 - 2 * γ) / 4 / (x - e₃) + (1 - 2 * δ) / 4 /
    (x - e₂) + (1 - 2 * ε) / 4 / (x - e₁)) / (e₂ - e₃) - (γ / ((x - e₃) / (e₂ - e₃)) +
    δ / ((x - e₂) / (e₂ - e₃)) + ε / ((x - e₁) / (e₂ - e₃))) / (e₂ - e₃) ^ 2) * hsq
  field_simp
  subst he₃
  ring

/-- Algebra of 31.2.9–31.2.12, zeroth-order coefficient. -/
lemma p3w_wf_algB {x y e₁ e₂ e₃ q α β γ δ ε : ℂ} (hs : e₁ + e₂ + e₃ = 0)
    (hF : α + β + 1 = γ + δ + ε)
    (h1 : x - e₁ ≠ 0) (h2 : x - e₂ ≠ 0) (h3 : x - e₃ ≠ 0) (hE : e₂ - e₃ ≠ 0)
    (hsq : y ^ 2 = 4 * (x - e₁) * (x - e₂) * (x - e₃)) :
    (e₁ * (γ + δ - 1) ^ 2 + e₂ * (γ + ε - 1) ^ 2 + e₃ * (δ + ε - 1) ^ 2 -
          4 * α * β * e₃ - 4 * q * (e₂ - e₃)) +
        (4 * α * β - (γ + δ + ε - 1 / 2) * (γ + δ + ε - 3 / 2)) * x -
        (ε - 1 / 2) * (ε - 3 / 2) * (y ^ 2 / (4 * (x - e₁) ^ 2) - x - e₁) -
        (δ - 1 / 2) * (δ - 3 / 2) * (y ^ 2 / (4 * (x - e₂) ^ 2) - x - e₂) -
        (γ - 1 / 2) * (γ - 3 / 2) * (y ^ 2 / (4 * (x - e₃) ^ 2) - x - e₃) +
      (-(y * ((1 - 2 * γ) / 4 / (x - e₃) + (1 - 2 * δ) / 4 / (x - e₂) +
        (1 - 2 * ε) / 4 / (x - e₁)))) ^ 2 +
      -((1 - 2 * γ) / 4 * ((6 * x ^ 2 - 2 * (e₁ ^ 2 + e₂ ^ 2 + e₃ ^ 2) / 2) * (x - e₃) - y ^ 2) /
          (x - e₃) ^ 2 +
        (1 - 2 * δ) / 4 * ((6 * x ^ 2 - 2 * (e₁ ^ 2 + e₂ ^ 2 + e₃ ^ 2) / 2) * (x - e₂) - y ^ 2) /
          (x - e₂) ^ 2 +
        (1 - 2 * ε) / 4 * ((6 * x ^ 2 - 2 * (e₁ ^ 2 + e₂ ^ 2 + e₃ ^ 2) / 2) * (x - e₁) - y ^ 2) /
          (x - e₁) ^ 2) =
      heunCoeffR ((e₁ - e₃) / (e₂ - e₃)) q α β ((x - e₃) / (e₂ - e₃)) * (y / (e₂ - e₃)) ^ 2 := by
  have hz1 : (x - e₃) / (e₂ - e₃) - 1 = (x - e₂) / (e₂ - e₃) := by field_simp; ring
  have hza : (x - e₃) / (e₂ - e₃) - (e₁ - e₃) / (e₂ - e₃) = (x - e₁) / (e₂ - e₃) := by ring
  simp only [heunCoeffR, hz1, hza]
  have he₃ : e₃ = -e₁ - e₂ := by linear_combination hs
  have hα : α = γ + δ + ε - 1 - β := by linear_combination hF
  linear_combination (norm := skip) (-(ε - 1 / 2) * (ε - 3 / 2) / (4 * (x - e₁) ^ 2) -
    (δ - 1 / 2) * (δ - 3 / 2) / (4 * (x - e₂) ^ 2) -
    (γ - 1 / 2) * (γ - 3 / 2) / (4 * (x - e₃) ^ 2) +
    ((1 - 2 * γ) / 4 / (x - e₃) + (1 - 2 * δ) / 4 / (x - e₂) + (1 - 2 * ε) / 4 / (x - e₁)) ^ 2 +
    ((1 - 2 * γ) / 4 / (x - e₃) ^ 2 + (1 - 2 * δ) / 4 / (x - e₂) ^ 2 +
      (1 - 2 * ε) / 4 / (x - e₁) ^ 2) -
    (α * β * ((x - e₃) / (e₂ - e₃)) - q) / ((x - e₃) / (e₂ - e₃) * ((x - e₂) / (e₂ - e₃)) *
      ((x - e₁) / (e₂ - e₃))) / (e₂ - e₃) ^ 2) * hsq
  field_simp
  subst he₃ hα
  ring

/-- Shift by a half period: `℘(z + ω_j) = ℘'(z)²/(4(℘(z) - e_j)²) - ℘(z) - e_j` (from 23.10.1). -/
lemma p3w_weierstrassP_add_halfPeriod (H : HalfPeriods) {j : ℕ}
    (hj : j ∈ ({1, 2, 3} : Finset ℕ)) {z : ℂ} (hz : z ∉ H.lattice)
    (hne : H.weierstrassP z ≠ H.e j) :
    H.weierstrassP (z + H.halfPeriod j) =
      H.derivWeierstrassP z ^ 2 / (4 * (H.weierstrassP z - H.e j) ^ 2) -
        H.weierstrassP z - H.e j := by
  have hv := H.halfPeriod_notMem hj
  have h1 : z + H.halfPeriod j ∉ H.lattice := by
    intro h; apply hne
    have e := H.periodPair.weierstrassP_sub_coe (H.halfPeriod j) ⟨_, h⟩
    simp only [show H.halfPeriod j - (z + H.halfPeriod j) = -z by ring,
      PeriodPair.weierstrassP_neg] at e
    exact e
  have h2 : z - H.halfPeriod j ∉ H.lattice := by
    intro h; apply hne
    have e := H.periodPair.weierstrassP_add_coe (H.halfPeriod j) ⟨_, h⟩
    simp only [show H.halfPeriod j + (z - H.halfPeriod j) = z by ring] at e
    exact e
  have h0 := H.derivWeierstrassP_halfPeriod hj
  have hne' : H.weierstrassP z - H.e j ≠ 0 := sub_ne_zero.mpr hne
  rw [HalfPeriods.weierstrassP, weierstrassP_add H.periodPair hz hv h1 h2]
  simp only [HalfPeriods.derivWeierstrassP] at h0
  simp only [HalfPeriods.e, HalfPeriods.weierstrassP, HalfPeriods.derivWeierstrassP, h0] at hne' ⊢
  field_simp
  ring

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
  obtain ⟨-, d23, -⟩ := L.e_distinct
  have hE : L.e 2 - L.e 3 ≠ 0 := sub_ne_zero.mpr d23
  have hs := L.e_sum
  have hg2 := L.g₂_eq_e.1
  have hn : ∀ ξ ∈ V, L.weierstrassP ξ - L.e 1 ≠ 0 ∧ L.weierstrassP ξ - L.e 2 ≠ 0 ∧
      L.weierstrassP ξ - L.e 3 ≠ 0 := fun ξ h => by
    obtain ⟨-, -, h1, h2, h3⟩ := hVU ξ h
    exact ⟨slitPlane_ne_zero h1, slitPlane_ne_zero h2, slitPlane_ne_zero h3⟩
  have hP : ∀ ξ ∈ V, HasDerivAt L.weierstrassP (L.derivWeierstrassP ξ) ξ := fun ξ h =>
    p23R1_hasDerivAt_wp L.periodPair (hVU ξ h).1
  have hD : ∀ ξ ∈ V, HasDerivAt L.derivWeierstrassP
      (6 * L.weierstrassP ξ ^ 2 - 2 * (L.e 1 ^ 2 + L.e 2 ^ 2 + L.e 3 ^ 2) / 2) ξ := fun ξ h => by
    rw [← hg2]; exact p23R1_hasDerivAt_dwp L.periodPair (hVU ξ h).1
  have hsq : ∀ ξ ∈ V, L.derivWeierstrassP ξ ^ 2 = 4 * (L.weierstrassP ξ - L.e 1) *
      (L.weierstrassP ξ - L.e 2) * (L.weierstrassP ξ - L.e 3) := fun ξ h =>
    L.derivWeierstrassP_sq_eq_prod (hVU ξ h).1
  set Sf : ℂ → ℂ := fun ξ => (1 - 2 * γ) / 4 / (L.weierstrassP ξ - L.e 3) +
    (1 - 2 * δ) / 4 / (L.weierstrassP ξ - L.e 2) +
    (1 - 2 * ε) / 4 / (L.weierstrassP ξ - L.e 1) with hSf
  set Lf : ℂ → ℂ := fun ξ => -(L.derivWeierstrassP ξ * Sf ξ) with hLf
  set Pdd : ℂ → ℂ := fun ξ => 6 * L.weierstrassP ξ ^ 2 -
    2 * (L.e 1 ^ 2 + L.e 2 ^ 2 + L.e 3 ^ 2) / 2 with hPdd
  set L'f : ℂ → ℂ := fun ξ =>
    -((1 - 2 * γ) / 4 * (Pdd ξ * (L.weierstrassP ξ - L.e 3) - L.derivWeierstrassP ξ ^ 2) /
          (L.weierstrassP ξ - L.e 3) ^ 2 +
        (1 - 2 * δ) / 4 * (Pdd ξ * (L.weierstrassP ξ - L.e 2) - L.derivWeierstrassP ξ ^ 2) /
          (L.weierstrassP ξ - L.e 2) ^ 2 +
        (1 - 2 * ε) / 4 * (Pdd ξ * (L.weierstrassP ξ - L.e 1) - L.derivWeierstrassP ξ ^ 2) /
          (L.weierstrassP ξ - L.e 1) ^ 2) with hL'f
  set Df : ℂ → ℂ := fun ξ => (L.weierstrassP ξ - L.e 3) ^ ((1 - 2 * γ) / 4) *
    (L.weierstrassP ξ - L.e 2) ^ ((1 - 2 * δ) / 4) *
    (L.weierstrassP ξ - L.e 1) ^ ((1 - 2 * ε) / 4) with hDf
  have hg : ∀ ξ ∈ V, HasDerivAt (fun ξ => (Df ξ)⁻¹) (Lf ξ * (Df ξ)⁻¹) ξ := fun ξ h => by
    obtain ⟨-, -, s1, s2, s3⟩ := hVU ξ h
    obtain ⟨n1, n2, n3⟩ := hn ξ h
    have hA := p1h_hasDerivAt_cpow (s := (1 - 2 * γ) / 4) ((hP ξ h).sub_const (L.e 3)) s3
    have hB := p1h_hasDerivAt_cpow (s := (1 - 2 * δ) / 4) ((hP ξ h).sub_const (L.e 2)) s2
    have hC := p1h_hasDerivAt_cpow (s := (1 - 2 * ε) / 4) ((hP ξ h).sub_const (L.e 1)) s1
    have c1 : (L.weierstrassP ξ - L.e 1) ^ ((1 - 2 * ε) / 4) ≠ 0 :=
      fun h0 => n1 ((cpow_eq_zero_iff _ _).mp h0).1
    have c2 : (L.weierstrassP ξ - L.e 2) ^ ((1 - 2 * δ) / 4) ≠ 0 :=
      fun h0 => n2 ((cpow_eq_zero_iff _ _).mp h0).1
    have c3 : (L.weierstrassP ξ - L.e 3) ^ ((1 - 2 * γ) / 4) ≠ 0 :=
      fun h0 => n3 ((cpow_eq_zero_iff _ _).mp h0).1
    have hD0 : Df ξ ≠ 0 := mul_ne_zero (mul_ne_zero c3 c2) c1
    convert ((hA.mul hB).mul hC).inv hD0 using 1
    simp only [hLf, hSf, hDf, Pi.mul_apply]
    field_simp
  have hL : ∀ ξ ∈ V, HasDerivAt Lf (L'f ξ) ξ := fun ξ h => by
    obtain ⟨n1, n2, n3⟩ := hn ξ h
    have hS : HasDerivAt Sf (-((1 - 2 * γ) / 4 * L.derivWeierstrassP ξ /
          (L.weierstrassP ξ - L.e 3) ^ 2 +
        (1 - 2 * δ) / 4 * L.derivWeierstrassP ξ / (L.weierstrassP ξ - L.e 2) ^ 2 +
        (1 - 2 * ε) / 4 * L.derivWeierstrassP ξ / (L.weierstrassP ξ - L.e 1) ^ 2)) ξ := by
      have a3 := (hasDerivAt_const ξ ((1 - 2 * γ) / 4)).div ((hP ξ h).sub_const (L.e 3)) n3
      have a2 := (hasDerivAt_const ξ ((1 - 2 * δ) / 4)).div ((hP ξ h).sub_const (L.e 2)) n2
      have a1 := (hasDerivAt_const ξ ((1 - 2 * ε) / 4)).div ((hP ξ h).sub_const (L.e 1)) n1
      convert (a3.add a2).add a1 using 1
      ring
    convert ((hD ξ h).mul hS).neg using 1
    simp only [hL'f, hPdd, hSf]
    field_simp
    ring
  rw [show (fun ξ => u ((L.weierstrassP ξ - L.e 3) / (L.e 2 - L.e 3)) / Df ξ) =
    fun ξ => (Df ξ)⁻¹ * u ((L.weierstrassP ξ - L.e 3) / (L.e 2 - L.e 3)) from
    funext fun ξ => div_eq_inv_mul _ _]
  refine p1h_isLinearODE2On_mul (p₁ := fun ξ => 2 * Lf ξ) (r₁ := _) hV hg hL
    (fun ξ _ => by simp) (fun _ _ => rfl) ?_
  refine p1h_isLinearODE2On_comp (φ₁ := fun ξ => L.derivWeierstrassP ξ / (L.e 2 - L.e 3))
    (φ₂ := fun ξ => Pdd ξ / (L.e 2 - L.e 3)) hV
    (fun ξ h => ((hP ξ h).sub_const _).div_const _) (fun ξ h => (hD ξ h).div_const _)
    (fun ξ h => (hVU ξ h).2.1) (fun ξ h => ?_) (fun ξ h => ?_) hu
  · obtain ⟨n1, n2, n3⟩ := hn ξ h
    exact p3w_wf_algA hs n1 n2 n3 hE (hsq ξ h)
  · obtain ⟨n1, n2, n3⟩ := hn ξ h
    have hx := (hVU ξ h).1
    have w1 := p3w_weierstrassP_add_halfPeriod L (j := 1) (by simp) hx (sub_ne_zero.mp n1)
    have w2 := p3w_weierstrassP_add_halfPeriod L (j := 2) (by simp) hx (sub_ne_zero.mp n2)
    have w3 := p3w_weierstrassP_add_halfPeriod L (j := 3) (by simp) hx (sub_ne_zero.mp n3)
    simp only [HalfPeriods.halfPeriod_one, HalfPeriods.halfPeriod_two,
      HalfPeriods.halfPeriod_three] at w1 w2 w3
    simp only [Pi.zero_apply, zero_mul, add_zero, w1, w2, w3]
    exact p3w_wf_algB hs hF n1 n2 n3 hE (hsq ξ h)

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

/-- Removable point for a second-order ODE: if `w` is analytic on the open set `V`, the
coefficients are continuous at `ζ₀`, and the equation holds on `V \ {ζ₀}`, it holds on `V`. -/
lemma p2h_isLinearODE2On_of_punctured {p r w : ℂ → ℂ} {V : Set ℂ} {ζ₀ : ℂ} (hV : IsOpen V)
    (hw : AnalyticOnNhd ℂ w V) (hp : ContinuousAt p ζ₀) (hr : ContinuousAt r ζ₀)
    (h : IsLinearODE2On p r w (V \ {ζ₀})) : IsLinearODE2On p r w V := by
  refine ⟨fun z hz => (hw z hz).differentiableAt, fun z hz => ?_⟩
  by_cases hz0 : z = ζ₀
  · subst hz0
    have hd : AnalyticAt ℂ (deriv w) z := (hw z hz).deriv
    refine hd.differentiableAt.hasDerivAt.congr_deriv ?_
    have hc1 : ContinuousAt (deriv (deriv w)) z := hd.deriv.continuousAt
    have hc2 : ContinuousAt (fun y => -(p y * deriv w y) - r y * w y) z :=
      (hp.mul hd.continuousAt).neg.sub (hr.mul (hw z hz).continuousAt)
    have hev : deriv (deriv w) =ᶠ[𝓝[≠] z] fun y => -(p y * deriv w y) - r y * w y := by
      have h1 : ∀ᶠ y in 𝓝[≠] z, y ∈ V :=
        eventually_nhdsWithin_of_eventually_nhds (hV.mem_nhds hz)
      filter_upwards [h1, self_mem_nhdsWithin] with y hy hy'
      exact (h.2 y ⟨hy, hy'⟩).deriv
    exact tendsto_nhds_unique (hc1.tendsto.mono_left nhdsWithin_le_nhds)
      ((hc2.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm)
  · exact h.2 z ⟨hz, hz0⟩

/-- A parameter with positive real part is not in `{0, -1, -2, …}`. -/
lemma p2h_ne_neg_nat_of_re_pos {c : ℂ} (hc : 0 < c.re) : ∀ n : ℕ, c ≠ -(n : ℂ) := by
  intro n h
  have := congrArg Complex.re h
  simp at this
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  linarith

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
  have hτ := jacobiTauk_im_pos hk
  have ha : (k ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hk0)
  have hR : 0 < heunLocalRadius (k ^ 2)⁻¹ := p1h_radius_pos ha
  have hθc : ContinuousAt (fun ζ => jacobiLetterTheta .n (jacobiZetak ζ k) (jacobiTauk k)) 0 := by
    simp only [jacobiLetterTheta, jacobiZetak]
    exact (((p22R1_hd4 hτ _).continuousAt).comp
      (by fun_prop : ContinuousAt (fun ζ : ℂ => π * ζ / (2 * compEllIntKk k)) 0)).div_const _
  have hθ0 : jacobiLetterTheta .n (jacobiZetak 0 k) (jacobiTauk k) ≠ 0 := by
    rw [show jacobiZetak 0 k = 0 by simp [jacobiZetak], je22a_letterTheta_zero hτ]
    simp
  have hsn0 := hasDerivAt_jacobiSnk hk hθ0
  have hcn0 := hasDerivAt_jacobiCnk hk hθ0
  have hdn0 := hasDerivAt_jacobiDnk hk hθ0
  rw [jacobiCnk_zero hk, jacobiDnk_zero hk] at hsn0
  have ev_cn : ∀ᶠ ζ in 𝓝 (0 : ℂ), jacobiCnk ζ k ≠ 0 :=
    hcn0.continuousAt.eventually_ne (by rw [jacobiCnk_zero hk]; exact one_ne_zero)
  have ev_dn : ∀ᶠ ζ in 𝓝 (0 : ℂ), jacobiDnk ζ k ≠ 0 :=
    hdn0.continuousAt.eventually_ne (by rw [jacobiDnk_zero hk]; exact one_ne_zero)
  have ev_sm : ∀ᶠ ζ in 𝓝 (0 : ℂ),
      jacobiSnk ζ k ^ 2 ∈ Metric.ball 0 (heunLocalRadius (k ^ 2)⁻¹) := by
    have ht : Tendsto (fun ζ => jacobiSnk ζ k ^ 2) (𝓝 0) (𝓝 0) := by
      have h2 : ContinuousAt (fun ζ => jacobiSnk ζ k ^ 2) 0 := hsn0.continuousAt.pow 2
      simpa [jacobiSnk_zero hk] using h2.tendsto
    exact ht.eventually (Metric.ball_mem_nhds 0 hR)
  have ev_ne : ∀ᶠ ζ in 𝓝 (0 : ℂ), ζ ≠ 0 → jacobiSnk ζ k ≠ 0 := by
    have := hsn0.eventually_ne (c := 0) (by norm_num : (1 : ℂ) * 1 ≠ 0)
    exact eventually_nhdsWithin_iff.1 this
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hθc.eventually_ne hθ0).and (ev_cn.and (ev_dn.and (ev_sm.and ev_ne))))
  set V := Metric.ball (0 : ℂ) ρ
  have hVo : IsOpen V := Metric.isOpen_ball
  have h0V : (0 : ℂ) ∈ V := Metric.mem_ball_self hρ
  have hV'o : IsOpen (V \ {0}) := hVo.sdiff isClosed_singleton
  have hUo : IsOpen (Metric.ball (0 : ℂ) (heunLocalRadius (k ^ 2)⁻¹) \ {0}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  have hsnA : AnalyticOnNhd ℂ (fun ζ => jacobiSnk ζ k) V :=
    DifferentiableOn.analyticOnNhd (fun ζ hζ =>
      (hasDerivAt_jacobiSnk hk (hball ζ hζ).1).differentiableAt.differentiableWithinAt) hVo
  have hVU : ∀ ζ ∈ V \ {0}, jacobiSnk ζ k ^ 2 ∈
      Metric.ball (0 : ℂ) (heunLocalRadius (k ^ 2)⁻¹) \ {0} ∧ jacobiSnk ζ k ≠ 0 ∧
        jacobiCnk ζ k ≠ 0 ∧ jacobiDnk ζ k ≠ 0 := fun ζ hζ => by
    obtain ⟨-, hc, hd, hs, hn⟩ := hball ζ hζ.1
    exact ⟨⟨hs, pow_ne_zero 2 (hn hζ.2)⟩, hn hζ.2, hc, hd⟩
  have hrc : ContinuousAt (fun ζ => h - ν * (ν + 1) * k ^ 2 * jacobiSnk ζ k ^ 2) 0 :=
    continuousAt_const.sub (continuousAt_const.mul
      (hsn0.continuousAt.pow 2 : ContinuousAt (fun ζ => jacobiSnk ζ k ^ 2) 0))
  have hcomp : ∀ {H : ℂ → ℂ}, AnalyticOnNhd ℂ H (Metric.ball 0 (heunLocalRadius (k ^ 2)⁻¹)) →
      AnalyticOnNhd ℂ (fun ζ => H (jacobiSnk ζ k ^ 2)) V := fun {H} hH ζ hζ => by
    have h2 : AnalyticAt ℂ (fun ζ => jacobiSnk ζ k ^ 2) ζ := (hsnA ζ hζ).pow 2
    exact AnalyticAt.comp (g := H) (f := fun ζ => jacobiSnk ζ k ^ 2)
      (hH _ (hball ζ hζ).2.2.2.1) h2
  have hγ1 := p2h_ne_neg_nat_of_re_pos (c := 1 / 2) (by norm_num)
  have hγ3 := p2h_ne_neg_nat_of_re_pos (c := 3 / 2) (by norm_num)
  have hsneg : ∀ ζ, jacobiSnk (-ζ) k = -jacobiSnk ζ k := fun ζ => by
    simp [jacobiSnk, jacobiPQk_neg]
  refine ⟨V, Metric.ball_mem_nhds 0 hρ, ⟨?_, ?_⟩, fun ζ _ _ => ⟨by rw [hsneg, neg_sq], hsneg ζ⟩⟩
  · obtain ⟨hA, hW⟩ := heunLocal_isHeunSolOn (q := -((k ^ 2)⁻¹ * h / 4)) (α := -ν / 2)
      (β := (ν + 1) / 2) (δ := 1 / 2) ha hγ1
    rw [show heunEps (-ν / 2) ((ν + 1) / 2) (1 / 2) (1 / 2) = 1 / 2 by unfold heunEps; ring]
      at hW
    exact p2h_isLinearODE2On_of_punctured hVo (hcomp hA) continuousAt_const hrc
      (heun_lame hk hk0 hUo hV'o hW hVU)
  · obtain ⟨hA, hW⟩ := heunLocal_isHeunSolOn (q := ((k ^ 2)⁻¹ + 1) / 4 - (k ^ 2)⁻¹ * h / 4)
      (α := (1 - ν) / 2) (β := (ν + 2) / 2) (δ := 1 / 2) ha hγ3
    rw [show heunEps ((1 - ν) / 2) ((ν + 2) / 2) (3 / 2) (1 / 2) = 1 / 2 by unfold heunEps; ring]
      at hW
    have J := heun_jacobiForm hk (by ring) hUo hV'o hW hVU
    refine p2h_isLinearODE2On_of_punctured hVo
      (fun ζ hζ => (hsnA ζ hζ).mul (hcomp hA ζ hζ)) continuousAt_const hrc ?_
    refine p1h_isLinearODE2On_mul hV'o (g := fun ζ => jacobiSnk ζ k)
      (L := fun ζ => jacobiCnk ζ k * jacobiDnk ζ k / jacobiSnk ζ k)
      (L' := fun ζ => -(jacobiDnk ζ k ^ 2 + k ^ 2 * jacobiCnk ζ k ^ 2) -
        jacobiCnk ζ k ^ 2 * jacobiDnk ζ k ^ 2 / jacobiSnk ζ k ^ 2)
      (fun ζ hζ => ?_) (fun ζ hζ => ?_) (fun ζ hζ => ?_) (fun ζ hζ => ?_) J
    · have hs := (hVU ζ hζ).2.1
      refine (hasDerivAt_jacobiSnk hk (hball ζ hζ.1).1).congr_deriv ?_
      field_simp
    · have hs := (hVU ζ hζ).2.1
      have hr := (hball ζ hζ.1).1
      refine (((hasDerivAt_jacobiCnk hk hr).mul (hasDerivAt_jacobiDnk hk hr)).div
        (hasDerivAt_jacobiSnk hk hr) hs).congr_deriv ?_
      simp only [Pi.mul_apply]
      field_simp
      ring
    · simp only [Pi.zero_apply]
      ring
    · have hs := (hVU ζ hζ).2.1
      obtain ⟨e1, e2⟩ := jacobi_sq_sum hk (hball ζ hζ.1).1
      simp only [Pi.zero_apply]
      field_simp
      linear_combination 4 * jacobiSnk ζ k ^ 2 * e2 + 4 * k ^ 2 * jacobiSnk ζ k ^ 2 * e1

end DLMF.Heun
