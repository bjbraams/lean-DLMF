/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.SpecialLattices

/-!
# Quarter periods (DLMF §23.7)

DLMF gives `℘(ω_j/2)` in two forms, a square-root form and a Jacobian form, with `k, k'` and
the square roots real and positive for rectangular lattices and "determined by continuity"
otherwise. Here the branch is made precise as follows.

* The Jacobian forms hold for every pair of generators with the lattice quantities
  `K = (π/2)θ₃²(0|τ)`, `k = θ₂²(0|τ)/θ₃²(0|τ)`, `k' = θ₄²(0|τ)/θ₃²(0|τ)` (these are the
  analytic continuations in `τ` of the rectangular values; checked numerically for several
  generator pairs of one lattice, including `τ` outside `-1 < ℜτ ≤ 1`).
* The squares of the square-root forms hold for every lattice, branch-free.
* For rectangular lattices the square-root forms hold with principal (positive) roots.
-/

@[expose] public section

open Complex PeriodPair DLMF.Elliptic DLMF.JacobiElliptic DLMF.Theta
open scoped Real

noncomputable section

namespace DLMF.Weierstrass

/-- For a half-lattice point `a`, `(℘(a/2) - ℘(a))² = (℘(b + a) - ℘(a))(℘(b) - ℘(a))` for every
`b` with `b, b + a ∉ 𝕃`. -/
lemma p23R1_weierstrassP_half_sub_sq (L : PeriodPair) {a b : ℂ} (ha : a ∉ L.lattice)
    (h2a : 2 * a ∈ L.lattice) (hb : b ∉ L.lattice) (hab : b + a ∉ L.lattice) :
    (℘[L] (a / 2) - ℘[L] a) ^ 2 = (℘[L] (b + a) - ℘[L] a) * (℘[L] b - ℘[L] a) := by
  obtain ⟨K, hK⟩ := p23R1_halfPeriod_product L ha h2a
  have h1 : a / 2 ∉ L.lattice := fun h => ha (by
    have := add_mem h h; rwa [add_halves] at this)
  have h2 : a / 2 + a ∉ L.lattice := fun h => ha (by
    have := sub_mem (add_mem h h) h2a
    rwa [show a / 2 + a + (a / 2 + a) - 2 * a = a by ring] at this)
  have h3 : ℘[L] (a / 2 + a) = ℘[L] (a / 2) := by
    rw [show a / 2 + a = -(a / 2) + ((⟨2 * a, h2a⟩ : L.lattice) : ℂ) by simp; ring,
      L.weierstrassP_add_coe, L.weierstrassP_neg]
  rw [hK b hb hab, ← hK _ h1 h2, h3, sq]

namespace HalfPeriods

variable (H : HalfPeriods)

/-- DLMF 23.7.1 (Jacobian form): `℘(ω₁/2) = e₁ + ω₁⁻²K²k'`. -/
@[dlmf 23.7.E1]
theorem weierstrassP_half_ω₁ :
    H.weierstrassP (H.ω₁ / 2) = H.e 1 + H.quarterK ^ 2 * H.comodulus / H.ω₁ ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz : H.ω₁ / 2 ∉ H.lattice := fun h =>
    H.halfPeriod_notMem (j := 1) (by simp) (by simpa using add_mem h h)
  have hθ := H.p23R1_thetaOne_ne_zero hz
  have hw : π * (H.ω₁ / 2) / (2 * H.ω₁) = π / 4 := by field_simp; ring
  rw [hw] at hθ
  have h2 : jacobiThetaTwoTau (π / 4) H.tau = jacobiThetaOneTau (π / 4) H.tau := by
    rw [(jacobiThetaTwoTau_half_periods _ _).1,
      show (π : ℂ) / 4 + π / 2 = -(π / 4) + π by ring, jacobiThetaOneTau_add_pi,
      jacobiThetaOneTau_neg, neg_neg]
  have h := H.p23R1_wp_sub_e_one hz
  rw [hw, h2] at h
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  rw [show H.weierstrassP (H.ω₁ / 2) = (H.weierstrassP (H.ω₁ / 2) - H.e 1) + H.e 1 by ring, h,
    quarterK, comodulus, compEllIntKTau, jacobiComodulusTau]
  field_simp
  ring

/-- DLMF 23.7.2 (Jacobian form): `℘(ω₂/2) = e₂ - iω₁⁻²K²kk'`. -/
@[dlmf 23.7.E2]
theorem weierstrassP_half_ω₂ :
    H.weierstrassP (H.ω₂ / 2) =
      H.e 2 - I * H.quarterK ^ 2 * H.modulus * H.comodulus / H.ω₁ ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz : H.ω₂ / 2 ∉ H.lattice := fun h =>
    H.halfPeriod_notMem (j := 2) (by simp) (by simpa using add_mem h h)
  have hθ := H.p23R1_thetaOne_ne_zero hz
  set d : ℂ := π / 4 + π * H.tau / 4 with hd
  have hw : π * (H.ω₂ / 2) / (2 * H.ω₁) = -d := by
    rw [hd, HalfPeriods.tau, HalfPeriods.ω₂]; field_simp; ring
  rw [hw, jacobiThetaOneTau_neg, neg_ne_zero] at hθ
  have a := (jacobiThetaThreeTau_half_periods (-d) H.tau).2.2
  rw [show -d + π / 2 + π * H.tau / 2 = d by rw [hd]; ring, thetaMultiplierM] at a
  have hM : cexp (I * -d + π * I * H.tau / 4) ^ 2 = -I := by
    rw [← exp_nat_mul, show ((2 : ℕ) : ℂ) * (I * -d + π * I * H.tau / 4) = -(π / 2 * I) by
      rw [hd]; push_cast; ring, exp_neg, th20_exp_pi_div_two_mul_I, inv_I]
  have h := H.p23R1_wp_sub_e_two hz
  rw [hw, jacobiThetaOneTau_neg, a] at h
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  rw [show H.weierstrassP (H.ω₂ / 2) = (H.weierstrassP (H.ω₂ / 2) - H.e 2) + H.e 2 by ring, h,
    quarterK, modulus, comodulus, compEllIntKTau, jacobiModulusTau, jacobiComodulusTau]
  generalize cexp (I * -d + π * I * H.tau / 4) = M at *
  generalize jacobiThetaOneTau d H.tau = T at *
  field_simp
  rw [hM]
  ring

/-- DLMF 23.7.3 (Jacobian form): `℘(ω₃/2) = e₃ - ω₁⁻²K²k`. -/
@[dlmf 23.7.E3]
theorem weierstrassP_half_ω₃ :
    H.weierstrassP (H.ω₃ / 2) = H.e 3 - H.quarterK ^ 2 * H.modulus / H.ω₁ ^ 2 := by
  have hω := H.ω₁_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz : H.ω₃ / 2 ∉ H.lattice := fun h =>
    H.halfPeriod_notMem (j := 3) (by simp) (by simpa using add_mem h h)
  have hθ := H.p23R1_thetaOne_ne_zero hz
  have hw : π * (H.ω₃ / 2) / (2 * H.ω₁) = π * H.tau / 4 := by
    rw [HalfPeriods.tau]; field_simp; ring
  rw [hw] at hθ
  have a := (jacobiThetaOneTau_half_periods (-(π * H.tau / 4)) H.tau).2.1
  rw [jacobiThetaOneTau_neg, show -(π * H.tau / 4) + π * H.tau / 2 = π * H.tau / 4 by ring,
    thetaMultiplierM, show I * -(π * H.tau / 4) + π * I * H.tau / 4 = 0 by ring, exp_zero,
    mul_one] at a
  have h := H.p23R1_wp_sub_e_three hz
  rw [hw] at h
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero H.tau_im_pos
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at n2 n3 n4
  have h1 : jacobiThetaOneTau (π * H.tau / 4) H.tau =
      I * jacobiThetaFourTau (π * H.tau / 4) H.tau := by
    linear_combination -a
  rw [show H.weierstrassP (H.ω₃ / 2) = (H.weierstrassP (H.ω₃ / 2) - H.e 3) + H.e 3 by ring, h, h1,
    quarterK, modulus, compEllIntKTau, jacobiModulusTau]
  have h4 : jacobiThetaFourTau (π * H.tau / 4) H.tau ≠ 0 := by
    intro h0; apply hθ; rw [h1, h0, mul_zero]
  field_simp
  rw [show (I : ℂ) ^ 2 = -1 from I_sq]
  ring

/-- DLMF 23.7.1–23.7.3 (square-root forms, squared; every lattice):
`(℘(ω₁/2) - e₁)² = (e₁ - e₃)(e₁ - e₂)`, `(℘(ω₂/2) - e₂)² = -(e₁ - e₂)(e₂ - e₃)`,
`(℘(ω₃/2) - e₃)² = (e₁ - e₃)(e₂ - e₃)`. -/
@[dlmf 23.7.E1, dlmf 23.7.E2, dlmf 23.7.E3]
theorem weierstrassP_half_sq :
    (H.weierstrassP (H.ω₁ / 2) - H.e 1) ^ 2 = (H.e 1 - H.e 3) * (H.e 1 - H.e 2) ∧
      (H.weierstrassP (H.ω₂ / 2) - H.e 2) ^ 2 = -((H.e 1 - H.e 2) * (H.e 2 - H.e 3)) ∧
      (H.weierstrassP (H.ω₃ / 2) - H.e 3) ^ 2 = (H.e 1 - H.e 3) * (H.e 2 - H.e 3) := by
  have hneg : ∀ j ∈ ({1, 2, 3} : Finset ℕ), -H.halfPeriod j ∉ H.lattice := fun j hj h =>
    H.halfPeriod_notMem hj (by simpa using neg_mem h)
  have key : ∀ j k l : ℕ, j ∈ ({1, 2, 3} : Finset ℕ) → k ∈ ({1, 2, 3} : Finset ℕ) →
      l ∈ ({1, 2, 3} : Finset ℕ) → H.halfPeriod k + H.halfPeriod j = -H.halfPeriod l →
      (H.weierstrassP (H.halfPeriod j / 2) - H.e j) ^ 2 = (H.e l - H.e j) * (H.e k - H.e j) := by
    intro j k l hj hk hl hjkl
    have := p23R1_weierstrassP_half_sub_sq H.periodPair (H.halfPeriod_notMem hj)
      (H.two_mul_halfPeriod_mem hj) (H.halfPeriod_notMem hk) (hjkl ▸ hneg l hl)
    rw [hjkl, PeriodPair.weierstrassP_neg] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · have := key 1 2 3 (by simp) (by simp) (by simp) (by simp [ω₂]; ring)
    simp only [halfPeriod_one] at this
    rw [this]; ring
  · have := key 2 3 1 (by simp) (by simp) (by simp) (by simp [ω₂])
    simp only [halfPeriod_two] at this
    rw [this]; ring
  · have := key 3 1 2 (by simp) (by simp) (by simp) (by simp [ω₂]; ring)
    simp only [halfPeriod_three] at this
    rw [this]; ring

/-- DLMF 23.7.1–23.7.3 (square-root forms, rectangular lattice, positive roots):
`℘(ω₁/2) = e₁ + √((e₁ - e₃)(e₁ - e₂))`, `℘(ω₂/2) = e₂ - i√((e₁ - e₂)(e₂ - e₃))`,
`℘(ω₃/2) = e₃ - √((e₁ - e₃)(e₂ - e₃))`. -/
@[dlmf 23.7.E1, dlmf 23.7.E2, dlmf 23.7.E3]
theorem IsRectangular.weierstrassP_half {H : HalfPeriods} (h : H.IsRectangular) :
    H.weierstrassP (H.ω₁ / 2) =
        H.e 1 + (Real.sqrt (((H.e 1 - H.e 3) * (H.e 1 - H.e 2)).re) : ℂ) ∧
      H.weierstrassP (H.ω₂ / 2) =
        H.e 2 - I * (Real.sqrt (((H.e 1 - H.e 2) * (H.e 2 - H.e 3)).re) : ℂ) ∧
      H.weierstrassP (H.ω₃ / 2) =
        H.e 3 - (Real.sqrt (((H.e 1 - H.e 3) * (H.e 2 - H.e 3)).re) : ℂ) := by
  obtain ⟨a, c, A, B, C, ha, hω, hcdef, hc, hA, hB, hC, hJ, e1, e2, e3, hK, hk, hk'⟩ :=
    p23R1_rect_data h
  have q1 := H.weierstrassP_half_ω₁
  have q2 := H.weierstrassP_half_ω₂
  have q3 := H.weierstrassP_half_ω₃
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hB0 : B ≠ 0 := by linarith
  have hcc : (c : ℂ) = (π : ℂ) ^ 2 / (4 * (a : ℂ) ^ 2) := by
    rw [hcdef]; push_cast; ring
  have s1 : Real.sqrt (((H.e 1 - H.e 3) * (H.e 1 - H.e 2)).re) = c * B ^ 2 * C ^ 2 := by
    rw [e1, e2, e3, ← ofReal_sub, ← ofReal_sub, ← ofReal_mul, ofReal_re]
    rw [show (c * (B ^ 4 + C ^ 4) / 3 - (c * (B ^ 4 + C ^ 4) / 3 - c * B ^ 4)) *
        (c * (B ^ 4 + C ^ 4) / 3 - (c * (B ^ 4 + C ^ 4) / 3 - c * C ^ 4)) =
        (c * B ^ 2 * C ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have s2 : Real.sqrt (((H.e 1 - H.e 2) * (H.e 2 - H.e 3)).re) = c * A ^ 2 * C ^ 2 := by
    rw [e1, e2, e3, ← ofReal_sub, ← ofReal_sub, ← ofReal_mul, ofReal_re]
    rw [show (c * (B ^ 4 + C ^ 4) / 3 - (c * (B ^ 4 + C ^ 4) / 3 - c * C ^ 4)) *
        (c * (B ^ 4 + C ^ 4) / 3 - c * C ^ 4 - (c * (B ^ 4 + C ^ 4) / 3 - c * B ^ 4)) =
        (c * A ^ 2 * C ^ 2) ^ 2 by linear_combination (c ^ 2 * C ^ 4) * hJ]
    exact Real.sqrt_sq (by positivity)
  have s3 : Real.sqrt (((H.e 1 - H.e 3) * (H.e 2 - H.e 3)).re) = c * A ^ 2 * B ^ 2 := by
    rw [e1, e2, e3, ← ofReal_sub, ← ofReal_sub, ← ofReal_mul, ofReal_re]
    rw [show (c * (B ^ 4 + C ^ 4) / 3 - (c * (B ^ 4 + C ^ 4) / 3 - c * B ^ 4)) *
        (c * (B ^ 4 + C ^ 4) / 3 - c * C ^ 4 - (c * (B ^ 4 + C ^ 4) / 3 - c * B ^ 4)) =
        (c * A ^ 2 * B ^ 2) ^ 2 by linear_combination (c ^ 2 * B ^ 4) * hJ]
    exact Real.sqrt_sq (by positivity)
  rw [s1, s2, s3]
  have hB0' : (B : ℂ) ≠ 0 := ofReal_ne_zero.mpr hB0
  refine ⟨?_, ?_, ?_⟩
  · rw [q1, hK, hk', hω]; push_cast; rw [hcc]; field_simp; ring
  · rw [q2, hK, hk, hk', hω]; push_cast; rw [hcc]; field_simp; ring
  · rw [q3, hK, hk, hω]; push_cast; rw [hcc]; field_simp; ring

end HalfPeriods

end DLMF.Weierstrass
