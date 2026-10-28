/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic
public import DLMF.Theta.Products
public import Mathlib.NumberTheory.ModularForms.DedekindEta

/-!
# Theta functions: identities (DLMF §§20.7–20.8)

Sums of squares, addition and duplication formulas, reduction formulas, Watson's identities, the
Landen transformations, the derivative of `θ₂/θ₄`, the transformations `τ ↦ τ + 1` and
`τ ↦ -1/τ` of the lattice parameter, and Watson's expansion 20.8.1.

DLMF writes most of these identities in the nome form `θⱼ(z, q)`, `θⱼ(z, q²)`, `θⱼ(z, iq)`.
Following DLMF's convention `q^α = e^{iαπτ}` they are stated in the lattice form: `q ↦ q²` is
`τ ↦ 2τ` and `q ↦ iq` is `τ ↦ τ + 1/2`. Quotients carry a nonvanishing hypothesis on their
denominator where it can vanish; theta constants `θ₂(0|τ), θ₃(0|τ), θ₄(0|τ)` never vanish for
`Im τ > 0` (`DLMF.Theta.jacobiThetaTau_eq_zero_iff`).

**Source correction (20.7.34).** With principal square roots the printed 20.7.34 holds only up to
sign: numerically (mpmath) it fails, e.g., for `τ = -2.19 + 1.29i` and `τ = 2.03 + 0.90i`, where the
left side equals minus the right side. We acquire the branch-free squared identity for all `τ`,
the printed form in the rectangular case `τ = it`, `t > 0`, where it holds, and the full-domain
corrected form `jacobiTheta_reduction_iq_eta`, in which the square root is the explicit
eta-quotient `e^{-iπ/8} η(τ)η(4τ)/η(2τ)` (checked with mpmath at 200 random points).

The transformations 20.7.26–20.7.33 are proved: `τ ↦ τ + 1` from the series, and `τ ↦ -1/τ` from
Mathlib's `jacobiTheta₂_functional_equation` and the half-period translations of §20.2(iii).
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic

/-! ### Helpers: Watson's product formula -/

/-- The parity splitting `(ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ`, `(j, k) ↦ (j + k, j - k)` on the left and
`(j, k) ↦ (j + k + 1, j - k)` on the right. -/
def p20R1_parityEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun := Sum.elim (fun p => (p.1 + p.2, p.1 - p.2)) (fun p => (p.1 + p.2 + 1, p.1 - p.2))
  invFun p := if (p.1 + p.2) % 2 = 0 then Sum.inl ((p.1 + p.2) / 2, (p.1 - p.2) / 2)
    else Sum.inr ((p.1 + p.2 - 1) / 2, (p.1 - p.2 - 1) / 2)
  left_inv := by
    rintro (⟨j, k⟩ | ⟨j, k⟩) <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> split_ifs with h
    · simp only [Sum.inl.injEq, Prod.mk.injEq]; omega
    · omega
    · omega
    · simp only [Sum.inr.injEq, Prod.mk.injEq]; omega
  right_inv := by
    rintro ⟨m, n⟩
    dsimp only
    split_ifs with h
    · simp only [Sum.elim_inl, Prod.mk.injEq]; omega
    · simp only [Sum.elim_inr, Prod.mk.injEq]; omega

/-- The series with terms `(fun n : ℤ => ‖jacobiTheta₂_term n z τ‖)` is summable. -/
lemma p20R1_summable_norm_term (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => ‖jacobiTheta₂_term n z τ‖) :=
  summable_norm_iff.mpr ((summable_jacobiTheta₂_term_iff z τ).mpr hτ)

/-- The series with terms `(fun p : ℤ × ℤ => jacobiTheta₂_term p.1 u τ * jacobiTheta₂_term p.2 v
σ)` converges to `(jacobiTheta₂ u τ * jacobiTheta₂ v σ)`. -/
lemma p20R1_hasSum_prod {u v τ σ : ℂ} (hτ : 0 < τ.im) (hσ : 0 < σ.im) :
    HasSum (fun p : ℤ × ℤ => jacobiTheta₂_term p.1 u τ * jacobiTheta₂_term p.2 v σ)
      (jacobiTheta₂ u τ * jacobiTheta₂ v σ) := by
  have h1 := hasSum_jacobiTheta₂_term u hτ
  have h2 := hasSum_jacobiTheta₂_term v hσ
  have hs : Summable (fun p : ℤ × ℤ => jacobiTheta₂_term p.1 u τ * jacobiTheta₂_term p.2 v σ) :=
    summable_mul_of_summable_norm (f := fun n : ℤ => jacobiTheta₂_term n u τ)
      (g := fun n : ℤ => jacobiTheta₂_term n v σ)
      (p20R1_summable_norm_term u hτ) (p20R1_summable_norm_term v hσ)
  exact h1.mul h2 hs

/-- Watson's product formula in Mathlib's normalization:
`ϑ(u|τ)ϑ(v|τ) = ϑ(u+v|2τ)ϑ(u-v|2τ) + e^{iπτ+2πiu} ϑ(u+v+τ|2τ)ϑ(u-v+τ|2τ)`. -/
lemma p20R1_jacobiTheta₂_mul (u v τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ u τ * jacobiTheta₂ v τ =
      jacobiTheta₂ (u + v) (2 * τ) * jacobiTheta₂ (u - v) (2 * τ) +
        cexp (π * I * τ + 2 * π * I * u) *
          (jacobiTheta₂ (u + v + τ) (2 * τ) * jacobiTheta₂ (u - v + τ) (2 * τ)) := by
  have h2τ : 0 < (2 * τ).im := by simp; linarith
  have hP := (p20R1_parityEquiv.hasSum_iff).mpr (p20R1_hasSum_prod (u := u) (v := v) hτ hτ)
  have hA : HasSum ((fun p : ℤ × ℤ => jacobiTheta₂_term p.1 u τ * jacobiTheta₂_term p.2 v τ) ∘
      p20R1_parityEquiv ∘ Sum.inl)
      (jacobiTheta₂ (u + v) (2 * τ) * jacobiTheta₂ (u - v) (2 * τ)) := by
    convert p20R1_hasSum_prod (u := u + v) (v := u - v) h2τ h2τ using 1
    funext p
    simp only [Function.comp_apply, p20R1_parityEquiv, Equiv.coe_fn_mk, Sum.elim_inl,
      jacobiTheta₂_term, ← exp_add]
    congr 1; push_cast; ring
  have hB : HasSum ((fun p : ℤ × ℤ => jacobiTheta₂_term p.1 u τ * jacobiTheta₂_term p.2 v τ) ∘
      p20R1_parityEquiv ∘ Sum.inr)
      (cexp (π * I * τ + 2 * π * I * u) *
          (jacobiTheta₂ (u + v + τ) (2 * τ) * jacobiTheta₂ (u - v + τ) (2 * τ))) := by
    convert (p20R1_hasSum_prod (u := u + v + τ) (v := u - v + τ) h2τ h2τ).mul_left
      (cexp (π * I * τ + 2 * π * I * u)) using 1
    funext p
    simp only [Function.comp_apply, p20R1_parityEquiv, Equiv.coe_fn_mk, Sum.elim_inr,
      jacobiTheta₂_term, ← exp_add]
    congr 1; push_cast; ring
  exact hP.unique (hA.sum hB)

/-- Watson's formula 20.7.14 in lattice form (helper). -/
theorem p20R1_W3 (z w τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau z τ * jacobiThetaThreeTau w τ =
      jacobiThetaThreeTau (z + w) (2 * τ) * jacobiThetaThreeTau (z - w) (2 * τ) +
        jacobiThetaTwoTau (z + w) (2 * τ) * jacobiThetaTwoTau (z - w) (2 * τ) := by
  have h := p20R1_jacobiTheta₂_mul (z / π) (w / π) τ hτ
  simp only [jacobiThetaThreeTau, jacobiThetaTwoTau]
  have a1 : z / π + w / π = (z + w) / π := by ring
  have a2 : z / π - w / π = (z - w) / π := by ring
  have a3 : z / π + w / π + τ = (z + w + π * (2 * τ) / 2) / π := by field_simp [pi_ne_zero']
  have a4 : z / π - w / π + τ = (z - w + π * (2 * τ) / 2) / π := by field_simp [pi_ne_zero']
  have a5 : cexp (π * I * τ + 2 * π * I * (z / π)) =
      cexp (π * I * (2 * τ) / 4 + I * (z + w)) * cexp (π * I * (2 * τ) / 4 + I * (z - w)) := by
    rw [← exp_add]; congr 1; field_simp [pi_ne_zero']; ring
  rw [a3, a4, a1, a2, a5] at h
  rw [h]; ring

/-- Watson-type formula for `θ₄θ₄` (helper). -/
lemma p20R1_W4 (z w τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaFourTau z τ * jacobiThetaFourTau w τ =
      jacobiThetaThreeTau (z + w) (2 * τ) * jacobiThetaThreeTau (z - w) (2 * τ) -
        jacobiThetaTwoTau (z + w) (2 * τ) * jacobiThetaTwoTau (z - w) (2 * τ) := by
  have h := p20R1_W3 (z + π / 2) (w + π / 2) τ hτ
  rw [show z + π / 2 + (w + π / 2) = z + w + π by ring,
    show z + π / 2 - (w + π / 2) = z - w by ring, jacobiThetaThreeTau_add_pi,
    jacobiThetaTwoTau_add_pi] at h
  rw [jacobiThetaFourTau, jacobiThetaFourTau, h]; ring

/-- Watson-type formula for `θ₂θ₂` (helper). -/
lemma p20R1_W2 (z w τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoTau z τ * jacobiThetaTwoTau w τ =
      jacobiThetaThreeTau (z + w) (2 * τ) * jacobiThetaTwoTau (z - w) (2 * τ) +
        jacobiThetaTwoTau (z + w) (2 * τ) * jacobiThetaThreeTau (z - w) (2 * τ) := by
  have h := p20R1_W3 (z + π * τ / 2) (-w + π * τ / 2) τ hτ
  rw [show z + π * τ / 2 + (-w + π * τ / 2) = z - w + π * (2 * τ) / 2 by ring,
    show z + π * τ / 2 - (-w + π * τ / 2) = z + w by ring] at h
  have hz := (jacobiThetaTwoTau_half_periods z τ).2.1
  have hw := (jacobiThetaTwoTau_half_periods (-w) τ).2.1
  rw [jacobiThetaTwoTau_neg] at hw
  have hA := (jacobiThetaTwoTau_half_periods (z - w) (2 * τ)).2.1
  have hB := (jacobiThetaThreeTau_half_periods (z - w) (2 * τ)).2.1
  have hM : thetaMultiplierM z τ * thetaMultiplierM (-w) τ = thetaMultiplierM (z - w) (2 * τ) := by
    simp only [thetaMultiplierM, ← exp_add]; congr 1; ring
  rw [hz, hw, hA, hB]
  linear_combination (thetaMultiplierM z τ * thetaMultiplierM (-w) τ) * h +
    (jacobiThetaThreeTau (z - w + π * (2 * τ) / 2) τ * 0) * hM +
    (jacobiThetaThreeTau (z + w) (2 * τ) * jacobiThetaThreeTau (z - w + π * (2 * τ) / 2) (2 * τ) +
      jacobiThetaTwoTau (z + w) (2 * τ) * jacobiThetaTwoTau (z - w + π * (2 * τ) / 2) (2 * τ)) * hM

/-- Watson's formula 20.7.13 for `θ₁θ₁` (helper). -/
lemma p20R1_W1 (z w τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaOneTau z τ * jacobiThetaOneTau w τ =
      jacobiThetaThreeTau (z + w) (2 * τ) * jacobiThetaTwoTau (z - w) (2 * τ) -
        jacobiThetaTwoTau (z + w) (2 * τ) * jacobiThetaThreeTau (z - w) (2 * τ) := by
  have h := p20R1_W2 (z + π / 2) (w - π / 2) τ hτ
  rw [show z + π / 2 + (w - π / 2) = z + w by ring,
    show z + π / 2 - (w - π / 2) = z - w + π by ring, jacobiThetaThreeTau_add_pi,
    jacobiThetaTwoTau_add_pi, (jacobiThetaTwoTau_half_periods (z + π / 2) τ).1,
    (jacobiThetaTwoTau_half_periods (w - π / 2) τ).1, show z + π / 2 + π / 2 = z + π by ring,
    show w - π / 2 + π / 2 = w by ring, jacobiThetaOneTau_add_pi] at h
  linear_combination -h

/-- `θ₁(0|τ) = 0` (helper). -/
lemma p20R1_one_zero (τ : ℂ) : jacobiThetaOneTau 0 τ = 0 := by
  have := jacobiThetaOneTau_neg 0 τ
  rw [neg_zero] at this
  exact CharZero.eq_neg_self_iff.mp this

/-- `θ₁(x + π/2|τ) = θ₂(x|τ)` (helper). -/
lemma p20R1_one_add_half (x τ : ℂ) : jacobiThetaOneTau (x + π / 2) τ = jacobiThetaTwoTau x τ :=
  (jacobiThetaTwoTau_half_periods x τ).1.symm

/-- `θ₂(x + π/2|τ) = -θ₁(x|τ)` (helper). -/
lemma p20R1_two_add_half (x τ : ℂ) : jacobiThetaTwoTau (x + π / 2) τ = -jacobiThetaOneTau x τ := by
  rw [jacobiThetaOneTau, neg_neg]

/-- `θ₃(x + π/2|τ) = θ₄(x|τ)` (helper). -/
lemma p20R1_three_add_half (x τ : ℂ) : jacobiThetaThreeTau (x + π / 2) τ = jacobiThetaFourTau x τ :=
  rfl

/-- `θ₄(x + π/2|τ) = θ₃(x|τ)` (helper). -/
lemma p20R1_four_add_half (x τ : ℂ) : jacobiThetaFourTau (x + π / 2) τ = jacobiThetaThreeTau x τ := by
  rw [jacobiThetaFourTau, show x + π / 2 + π / 2 = x + π by ring, jacobiThetaThreeTau_add_pi]

/-- `θ₂(π/2|τ) = 0` (helper). -/
lemma p20R1_two_half_pi (τ : ℂ) : jacobiThetaTwoTau (π / 2) τ = 0 := by
  rw [show (π / 2 : ℂ) = 0 + π / 2 by ring, p20R1_two_add_half, p20R1_one_zero, neg_zero]

/-- `θ₃(π/2|τ) = θ₄(0|τ)` (helper). -/
lemma p20R1_three_half_pi (τ : ℂ) : jacobiThetaThreeTau (π / 2) τ = jacobiThetaFourNullTau τ := by
  rw [show (π / 2 : ℂ) = 0 + π / 2 by ring, p20R1_three_add_half]

/-- The quartic identity `θ₃²(z)θ₃²(w) - θ₄²(z)θ₄²(w) = θ₂²(z)θ₂²(w) - θ₁²(z)θ₁²(w)` (helper). -/
lemma p20R1_quartic (z w τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau z τ ^ 2 * jacobiThetaThreeTau w τ ^ 2 -
      jacobiThetaFourTau z τ ^ 2 * jacobiThetaFourTau w τ ^ 2 =
    jacobiThetaTwoTau z τ ^ 2 * jacobiThetaTwoTau w τ ^ 2 -
      jacobiThetaOneTau z τ ^ 2 * jacobiThetaOneTau w τ ^ 2 := by
  have h3 := p20R1_W3 z w τ hτ
  have h4 := p20R1_W4 z w τ hτ
  have h2 := p20R1_W2 z w τ hτ
  have h1 := p20R1_W1 z w τ hτ
  linear_combination (jacobiThetaThreeTau z τ * jacobiThetaThreeTau w τ +
      (jacobiThetaThreeTau (z + w) (2 * τ) * jacobiThetaThreeTau (z - w) (2 * τ) +
        jacobiThetaTwoTau (z + w) (2 * τ) * jacobiThetaTwoTau (z - w) (2 * τ))) * h3 -
    (jacobiThetaFourTau z τ * jacobiThetaFourTau w τ +
      (jacobiThetaThreeTau (z + w) (2 * τ) * jacobiThetaThreeTau (z - w) (2 * τ) -
        jacobiThetaTwoTau (z + w) (2 * τ) * jacobiThetaTwoTau (z - w) (2 * τ))) * h4 -
    (jacobiThetaTwoTau z τ * jacobiThetaTwoTau w τ +
      (jacobiThetaThreeTau (z + w) (2 * τ) * jacobiThetaTwoTau (z - w) (2 * τ) +
        jacobiThetaTwoTau (z + w) (2 * τ) * jacobiThetaThreeTau (z - w) (2 * τ))) * h2 +
    (jacobiThetaOneTau z τ * jacobiThetaOneTau w τ +
      (jacobiThetaThreeTau (z + w) (2 * τ) * jacobiThetaTwoTau (z - w) (2 * τ) -
        jacobiThetaTwoTau (z + w) (2 * τ) * jacobiThetaThreeTau (z - w) (2 * τ))) * h1

/-- Algebraic step for the addition formulas 20.7.6–20.7.9 (helper). -/
lemma p20R1_alg {n p₁ p₂ u v r t X Y a b c d : ℂ} (hP : p₁ * p₂ = X) (hN : n * n = Y)
    (h1 : u * u = a) (h2 : v * v = b) (h3 : r * r = c) (h4 : t * t = d)
    (hid : Y * X = a * b - c * d) : n ^ 2 * p₁ * p₂ = u ^ 2 * v ^ 2 - r ^ 2 * t ^ 2 := by
  calc n ^ 2 * p₁ * p₂ = (n * n) * (p₁ * p₂) := by ring
    _ = a * b - c * d := by rw [hN, hP, hid]
    _ = u ^ 2 * v ^ 2 - r ^ 2 * t ^ 2 := by rw [← h1, ← h2, ← h3, ← h4]; ring

/-- Landen-type product `θ₁(z|τ)θ₂(z|τ) = θ₁(2z|2τ)θ₄(0|2τ)` (helper). -/
theorem p20R1_L1 (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaOneTau z τ * jacobiThetaTwoTau z τ =
      jacobiThetaOneTau (2 * z) (2 * τ) * jacobiThetaFourNullTau (2 * τ) := by
  have h := p20R1_W1 z (z + π / 2) τ hτ
  rw [p20R1_one_add_half, show z + (z + π / 2) = 2 * z + π / 2 by ring,
    show z - (z + π / 2) = -(π / 2) by ring, jacobiThetaTwoTau_neg, jacobiThetaThreeTau_neg,
    p20R1_two_half_pi, p20R1_three_half_pi, p20R1_two_add_half] at h
  linear_combination h

/-- Landen-type product `θ₃(z|τ)θ₄(z|τ) = θ₄(2z|2τ)θ₄(0|2τ)` (helper). -/
theorem p20R1_L4 (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau z τ * jacobiThetaFourTau z τ =
      jacobiThetaFourTau (2 * z) (2 * τ) * jacobiThetaFourNullTau (2 * τ) := by
  have h := p20R1_W3 z (z + π / 2) τ hτ
  rw [p20R1_three_add_half, show z + (z + π / 2) = 2 * z + π / 2 by ring,
    show z - (z + π / 2) = -(π / 2) by ring, jacobiThetaTwoTau_neg, jacobiThetaThreeTau_neg,
    p20R1_two_half_pi, p20R1_three_half_pi, p20R1_three_add_half] at h
  linear_combination h

/-- Landen-type product `θ₁(π/4-z|τ)θ₁(π/4+z|τ) = θ₄(0|2τ)θ₂(2z|2τ)` (helper). -/
lemma p20R1_L2 (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaOneTau (π / 4 - z) τ * jacobiThetaOneTau (π / 4 + z) τ =
      jacobiThetaFourNullTau (2 * τ) * jacobiThetaTwoTau (2 * z) (2 * τ) := by
  have h := p20R1_W1 (π / 4 - z) (π / 4 + z) τ hτ
  rw [show π / 4 - z + (π / 4 + z) = π / 2 by ring, show π / 4 - z - (π / 4 + z) = -(2 * z) by ring,
    jacobiThetaTwoTau_neg, jacobiThetaThreeTau_neg, p20R1_two_half_pi, p20R1_three_half_pi] at h
  linear_combination h

/-- Landen-type product `θ₃(π/4-z|τ)θ₃(π/4+z|τ) = θ₄(0|2τ)θ₃(2z|2τ)` (helper). -/
lemma p20R1_L3 (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau (π / 4 - z) τ * jacobiThetaThreeTau (π / 4 + z) τ =
      jacobiThetaFourNullTau (2 * τ) * jacobiThetaThreeTau (2 * z) (2 * τ) := by
  have h := p20R1_W3 (π / 4 - z) (π / 4 + z) τ hτ
  rw [show π / 4 - z + (π / 4 + z) = π / 2 by ring, show π / 4 - z - (π / 4 + z) = -(2 * z) by ring,
    jacobiThetaTwoTau_neg, jacobiThetaThreeTau_neg, p20R1_two_half_pi, p20R1_three_half_pi] at h
  linear_combination h

/-- `2 θ₁(x|2τ)θ₄(x|2τ) = θ₁(x|τ)θ₂(0|τ)` (helper, 20.7.12). -/
lemma p20R1_D1 (x τ : ℂ) (hτ : 0 < τ.im) :
    2 * (jacobiThetaOneTau x (2 * τ) * jacobiThetaFourTau x (2 * τ)) =
      jacobiThetaOneTau x τ * jacobiThetaTwoNullTau τ := by
  have h := p20R1_W2 (x + π / 2) 0 τ hτ
  rw [add_zero, sub_zero] at h
  simp only [p20R1_two_add_half, p20R1_three_add_half] at h
  linear_combination h

/-- `2 θ₂(x|2τ)θ₃(x|2τ) = θ₂(x|τ)θ₂(0|τ)` (helper, 20.7.12). -/
lemma p20R1_D2 (x τ : ℂ) (hτ : 0 < τ.im) :
    2 * (jacobiThetaTwoTau x (2 * τ) * jacobiThetaThreeTau x (2 * τ)) =
      jacobiThetaTwoTau x τ * jacobiThetaTwoNullTau τ := by
  have h := p20R1_W2 x 0 τ hτ
  rw [add_zero, sub_zero] at h
  linear_combination -h

/-- `θ₃(0|τ)θ₄(0|τ) = θ₄(0|2τ)²` (helper). -/
theorem p20R1_L40 (τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ =
      jacobiThetaFourNullTau (2 * τ) * jacobiThetaFourNullTau (2 * τ) := by
  have h := p20R1_L4 0 τ hτ
  rwa [mul_zero] at h

/-- DLMF 20.7.4, used for 20.7.3 (helper). -/
lemma p20R1_sq23 (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoNullTau τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 =
      jacobiThetaFourNullTau τ ^ 2 * jacobiThetaOneTau z τ ^ 2 +
        jacobiThetaThreeNullTau τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 := by
  have h := p20R1_quartic (z + π * τ / 2) 0 τ hτ
  rw [p20R1_one_zero] at h
  have hA := (jacobiThetaTwoTau_half_periods z τ).2.1
  have hB := (jacobiThetaThreeTau_half_periods z τ).2.1
  have hC := (jacobiThetaOneTau_half_periods z τ).2.1
  rw [hA, hB, hC]
  linear_combination (-(thetaMultiplierM z τ) ^ 2) * h +
    (-(jacobiThetaFourNullTau τ ^ 2 * thetaMultiplierM z τ ^ 2 *
      jacobiThetaFourTau (z + π * τ / 2) τ ^ 2)) * I_sq

/-- The parity splitting `ℤ ⊕ ℤ ≃ ℤ`, `j ↦ 2j` on the left and `j ↦ 2j + 1` on the right. -/
def p20R1_parityEquivInt : ℤ ⊕ ℤ ≃ ℤ where
  toFun := Sum.elim (fun j => 2 * j) (fun j => 2 * j + 1)
  invFun n := if n % 2 = 0 then Sum.inl (n / 2) else Sum.inr (n / 2)
  left_inv := by
    rintro (j | j) <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> split_ifs with h
    · simp only [Sum.inl.injEq]; omega
    · omega
    · omega
    · simp only [Sum.inr.injEq]; omega
  right_inv := by
    intro n
    dsimp only
    split_ifs with h
    · simp only [Sum.elim_inl]; omega
    · simp only [Sum.elim_inr]; omega

/-- Even/odd splitting `ϑ(u|τ) = ϑ(2u|4τ) + e^{iπτ+2πiu} ϑ(2u+2τ|4τ)` (helper). -/
lemma p20R1_jacobiTheta₂_split (u τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ u τ = jacobiTheta₂ (2 * u) (4 * τ) +
      cexp (π * I * τ + 2 * π * I * u) * jacobiTheta₂ (2 * u + 2 * τ) (4 * τ) := by
  have h4τ : 0 < (4 * τ).im := by simp; linarith
  have hP := (p20R1_parityEquivInt.hasSum_iff).mpr (hasSum_jacobiTheta₂_term u hτ)
  have hA : HasSum ((fun n : ℤ => jacobiTheta₂_term n u τ) ∘ p20R1_parityEquivInt ∘ Sum.inl)
      (jacobiTheta₂ (2 * u) (4 * τ)) := by
    convert hasSum_jacobiTheta₂_term (2 * u) h4τ using 1
    funext j
    simp only [Function.comp_apply, p20R1_parityEquivInt, Equiv.coe_fn_mk, Sum.elim_inl,
      jacobiTheta₂_term]
    congr 1; push_cast; ring
  have hB : HasSum ((fun n : ℤ => jacobiTheta₂_term n u τ) ∘ p20R1_parityEquivInt ∘ Sum.inr)
      (cexp (π * I * τ + 2 * π * I * u) * jacobiTheta₂ (2 * u + 2 * τ) (4 * τ)) := by
    convert (hasSum_jacobiTheta₂_term (2 * u + 2 * τ) h4τ).mul_left
      (cexp (π * I * τ + 2 * π * I * u)) using 1
    funext j
    simp only [Function.comp_apply, p20R1_parityEquivInt, Equiv.coe_fn_mk, Sum.elim_inr,
      jacobiTheta₂_term, ← exp_add]
    congr 1; push_cast; ring
  exact hP.unique (hA.sum hB)

/-- `θ₃(z|τ) = θ₃(2z|4τ) + θ₂(2z|4τ)` (helper). -/
lemma p20R1_three_split (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau z τ = jacobiThetaThreeTau (2 * z) (4 * τ) +
      jacobiThetaTwoTau (2 * z) (4 * τ) := by
  have h := p20R1_jacobiTheta₂_split (z / π) τ hτ
  simp only [jacobiThetaThreeTau, jacobiThetaTwoTau]
  rw [h, show 2 * (z / π) + 2 * τ = (2 * z + π * (4 * τ) / 2) / π by field_simp; ring,
    show 2 * (z / π) = 2 * z / π by ring]
  congr 2
  congr 1; field_simp

/-- `θ₃(π/4|τ) = θ₄(0|4τ)` (helper). -/
lemma p20R1_three_quarter (τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau (π / 4) τ = jacobiThetaFourNullTau (4 * τ) := by
  rw [p20R1_three_split _ τ hτ, show 2 * (π / 4 : ℂ) = π / 2 by ring, p20R1_two_half_pi,
    p20R1_three_half_pi, add_zero]

/-- `θ₄(π/4 - a|τ) = θ₃(π/4 + a|τ)` (helper). -/
lemma p20R1_four_quarter_sub (a τ : ℂ) :
    jacobiThetaFourTau (π / 4 - a) τ = jacobiThetaThreeTau (π / 4 + a) τ := by
  rw [jacobiThetaFourTau, show π / 4 + a = -(π / 4 - a + π / 2) + π by ring,
    jacobiThetaThreeTau_add_pi, jacobiThetaThreeTau_neg]

/-- `θ₄(π/4 + a|τ) = θ₃(π/4 - a|τ)` (helper). -/
lemma p20R1_four_quarter_add (a τ : ℂ) :
    jacobiThetaFourTau (π / 4 + a) τ = jacobiThetaThreeTau (π / 4 - a) τ := by
  rw [jacobiThetaFourTau, show π / 4 - a = -(π / 4 + a + π / 2) + π by ring,
    jacobiThetaThreeTau_add_pi, jacobiThetaThreeTau_neg]

/-- `θ₂(3π/8 + z|τ) = θ₁(π/8 - z|τ)` (helper). -/
lemma p20R1_two_eighth_add (z τ : ℂ) :
    jacobiThetaTwoTau (3 * π / 8 + z) τ = jacobiThetaOneTau (π / 8 - z) τ := by
  rw [← p20R1_one_add_half, show 3 * π / 8 + z + π / 2 = -(π / 8 - z) + π by ring,
    jacobiThetaOneTau_add_pi, jacobiThetaOneTau_neg, neg_neg]

/-- `θ₂(3π/8 - z|τ) = θ₁(π/8 + z|τ)` (helper). -/
lemma p20R1_two_eighth_sub (z τ : ℂ) :
    jacobiThetaTwoTau (3 * π / 8 - z) τ = jacobiThetaOneTau (π / 8 + z) τ := by
  rw [← p20R1_one_add_half, show 3 * π / 8 - z + π / 2 = -(π / 8 + z) + π by ring,
    jacobiThetaOneTau_add_pi, jacobiThetaOneTau_neg, neg_neg]

/-- `θ₃(3π/8 + z|τ) = θ₄(π/8 - z|τ)` (helper). -/
lemma p20R1_three_eighth_add (z τ : ℂ) :
    jacobiThetaThreeTau (3 * π / 8 + z) τ = jacobiThetaFourTau (π / 8 - z) τ := by
  rw [← jacobiThetaFourTau_neg, jacobiThetaFourTau]; congr 1; ring

/-- `θ₃(3π/8 - z|τ) = θ₄(π/8 + z|τ)` (helper). -/
lemma p20R1_three_eighth_sub (z τ : ℂ) :
    jacobiThetaThreeTau (3 * π / 8 - z) τ = jacobiThetaFourTau (π / 8 + z) τ := by
  rw [jacobiThetaFourTau, ← jacobiThetaThreeTau_neg (3 * π / 8 - z), ← jacobiThetaThreeTau_add_pi]
  congr 1; ring

/-- The nonvanishing of the Landen constant `B` denominators (helper). -/
lemma p20R1_landenB_ne (τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ * jacobiThetaThreeTau (π / 4) τ ≠ 0 := by
  obtain ⟨-, n3, n4⟩ := jacobiThetaNullTau_ne_zero hτ
  have n44 := (jacobiThetaNullTau_ne_zero (τ := 4 * τ) (by simp; linarith)).2.2
  rw [p20R1_three_quarter τ hτ]
  exact mul_ne_zero (mul_ne_zero n3 n4) n44

/-! ### §20.7(i) Sums of squares -/

/-- DLMF 20.7.1: `θ₃²(0) θ₃²(z) = θ₄²(0) θ₄²(z) + θ₂²(0) θ₂²(z)`. -/
@[dlmf 20.7.E1]
theorem jacobiTheta_sq_three_three (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeNullTau τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 =
      jacobiThetaFourNullTau τ ^ 2 * jacobiThetaFourTau z τ ^ 2 +
        jacobiThetaTwoNullTau τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 := by
  have h := p20R1_quartic z 0 τ hτ
  rw [p20R1_one_zero] at h
  linear_combination h

/-- DLMF 20.7.2: `θ₃²(0) θ₄²(z) = θ₂²(0) θ₁²(z) + θ₄²(0) θ₃²(z)`. -/
@[dlmf 20.7.E2]
theorem jacobiTheta_sq_three_four (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeNullTau τ ^ 2 * jacobiThetaFourTau z τ ^ 2 =
      jacobiThetaTwoNullTau τ ^ 2 * jacobiThetaOneTau z τ ^ 2 +
        jacobiThetaFourNullTau τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 := by
  have h := p20R1_quartic (z + π / 2) 0 τ hτ
  rw [p20R1_three_add_half, p20R1_four_add_half, p20R1_two_add_half, p20R1_one_add_half,
    p20R1_one_zero] at h
  linear_combination h

/-- DLMF 20.7.3: `θ₂²(0) θ₄²(z) = θ₃²(0) θ₁²(z) + θ₄²(0) θ₂²(z)`. -/
@[dlmf 20.7.E3]
theorem jacobiTheta_sq_two_four (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoNullTau τ ^ 2 * jacobiThetaFourTau z τ ^ 2 =
      jacobiThetaThreeNullTau τ ^ 2 * jacobiThetaOneTau z τ ^ 2 +
        jacobiThetaFourNullTau τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 := by
  have h := p20R1_sq23 (z + π / 2) τ hτ
  rw [p20R1_three_add_half, p20R1_one_add_half, p20R1_two_add_half] at h
  linear_combination h

/-- DLMF 20.7.4: `θ₂²(0) θ₃²(z) = θ₄²(0) θ₁²(z) + θ₃²(0) θ₂²(z)`. -/
@[dlmf 20.7.E4]
theorem jacobiTheta_sq_two_three (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoNullTau τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 =
      jacobiThetaFourNullTau τ ^ 2 * jacobiThetaOneTau z τ ^ 2 +
        jacobiThetaThreeNullTau τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 := by
  exact p20R1_sq23 z τ hτ

/-- DLMF 20.7.5 (Jacobi's identity): `θ₃⁴(0) = θ₂⁴(0) + θ₄⁴(0)`; the case `z = 0` of 20.7.1. -/
@[dlmf 20.7.E5]
theorem jacobiThetaNull_fourth_power (τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeNullTau τ ^ 4 = jacobiThetaTwoNullTau τ ^ 4 + jacobiThetaFourNullTau τ ^ 4 := by
  have h := jacobiTheta_sq_three_three 0 τ hτ
  linear_combination h

/-! ### §20.7(ii) Addition formulas -/

/-- DLMF 20.7.6: `θ₄²(0) θ₁(w+z) θ₁(w-z) = θ₃²(w) θ₂²(z) - θ₂²(w) θ₃²(z)`. -/
@[dlmf 20.7.E6]
theorem jacobiThetaOneTau_add_mul_sub (w z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaFourNullTau τ ^ 2 * jacobiThetaOneTau (w + z) τ * jacobiThetaOneTau (w - z) τ =
      jacobiThetaThreeTau w τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 -
        jacobiThetaTwoTau w τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 := by
  have hP := p20R1_W1 (w + z) (w - z) τ hτ
  rw [show w + z + (w - z) = 2 * w by ring, show w + z - (w - z) = 2 * z by ring] at hP
  have hN := p20R1_W4 0 0 τ hτ
  have h1 := p20R1_W3 w w τ hτ
  have h2 := p20R1_W2 z z τ hτ
  have h3 := p20R1_W2 w w τ hτ
  have h4 := p20R1_W3 z z τ hτ
  rw [add_zero, sub_zero] at hN
  rw [← two_mul, sub_self] at h1 h2 h3 h4
  exact p20R1_alg hP hN h1 h2 h3 h4 (by ring)

/-- DLMF 20.7.7: `θ₄²(0) θ₂(w+z) θ₂(w-z) = θ₄²(w) θ₂²(z) - θ₁²(w) θ₃²(z)`. -/
@[dlmf 20.7.E7]
theorem jacobiThetaTwoTau_add_mul_sub (w z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaFourNullTau τ ^ 2 * jacobiThetaTwoTau (w + z) τ * jacobiThetaTwoTau (w - z) τ =
      jacobiThetaFourTau w τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 -
        jacobiThetaOneTau w τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 := by
  have hP := p20R1_W2 (w + z) (w - z) τ hτ
  rw [show w + z + (w - z) = 2 * w by ring, show w + z - (w - z) = 2 * z by ring] at hP
  have hN := p20R1_W4 0 0 τ hτ
  have h1 := p20R1_W4 w w τ hτ
  have h2 := p20R1_W2 z z τ hτ
  have h3 := p20R1_W1 w w τ hτ
  have h4 := p20R1_W3 z z τ hτ
  rw [add_zero, sub_zero] at hN
  rw [← two_mul, sub_self] at h1 h2 h3 h4
  exact p20R1_alg hP hN h1 h2 h3 h4 (by ring)

/-- DLMF 20.7.8: `θ₄²(0) θ₃(w+z) θ₃(w-z) = θ₄²(w) θ₃²(z) - θ₁²(w) θ₂²(z)`. -/
@[dlmf 20.7.E8]
theorem jacobiThetaThreeTau_add_mul_sub (w z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaFourNullTau τ ^ 2 * jacobiThetaThreeTau (w + z) τ * jacobiThetaThreeTau (w - z) τ =
      jacobiThetaFourTau w τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 -
        jacobiThetaOneTau w τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 := by
  have hP := p20R1_W3 (w + z) (w - z) τ hτ
  rw [show w + z + (w - z) = 2 * w by ring, show w + z - (w - z) = 2 * z by ring] at hP
  have hN := p20R1_W4 0 0 τ hτ
  have h1 := p20R1_W4 w w τ hτ
  have h2 := p20R1_W3 z z τ hτ
  have h3 := p20R1_W1 w w τ hτ
  have h4 := p20R1_W2 z z τ hτ
  rw [add_zero, sub_zero] at hN
  rw [← two_mul, sub_self] at h1 h2 h3 h4
  exact p20R1_alg hP hN h1 h2 h3 h4 (by ring)

/-- DLMF 20.7.9: `θ₄²(0) θ₄(w+z) θ₄(w-z) = θ₃²(w) θ₃²(z) - θ₂²(w) θ₂²(z)`. -/
@[dlmf 20.7.E9]
theorem jacobiThetaFourTau_add_mul_sub (w z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaFourNullTau τ ^ 2 * jacobiThetaFourTau (w + z) τ * jacobiThetaFourTau (w - z) τ =
      jacobiThetaThreeTau w τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 -
        jacobiThetaTwoTau w τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 := by
  have hP := p20R1_W4 (w + z) (w - z) τ hτ
  rw [show w + z + (w - z) = 2 * w by ring, show w + z - (w - z) = 2 * z by ring] at hP
  have hN := p20R1_W4 0 0 τ hτ
  have h1 := p20R1_W3 w w τ hτ
  have h2 := p20R1_W3 z z τ hτ
  have h3 := p20R1_W2 w w τ hτ
  have h4 := p20R1_W2 z z τ hτ
  rw [add_zero, sub_zero] at hN
  rw [← two_mul, sub_self] at h1 h2 h3 h4
  exact p20R1_alg hP hN h1 h2 h3 h4 (by ring)

/-! ### §20.7(iii) Duplication formula -/

/-- DLMF 20.7.10: `θ₁(2z) = 2 θ₁(z) θ₂(z) θ₃(z) θ₄(z) / (θ₂(0) θ₃(0) θ₄(0))`, `Im τ > 0`. -/
@[dlmf 20.7.E10]
theorem jacobiThetaOneTau_two_mul (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaOneTau (2 * z) τ = 2 * (jacobiThetaOneTau z τ * jacobiThetaTwoTau z τ *
      jacobiThetaThreeTau z τ * jacobiThetaFourTau z τ) /
        (jacobiThetaTwoNullTau τ * jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ) := by
  have h2τ : 0 < (2 * τ).im := by simp; linarith
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero hτ
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero n2 n3) n4)]
  have hL1 := p20R1_L1 z τ hτ
  have hL4 := p20R1_L4 z τ hτ
  have hL40 := p20R1_L40 τ hτ
  have hD1 := p20R1_D1 (2 * z) τ hτ
  linear_combination (jacobiThetaOneTau (2 * z) τ * jacobiThetaTwoNullTau τ) * hL40 -
    (jacobiThetaFourNullTau (2 * τ) * jacobiThetaFourNullTau (2 * τ)) * hD1 -
    (2 * jacobiThetaThreeTau z τ * jacobiThetaFourTau z τ) * hL1 -
    (2 * jacobiThetaOneTau (2 * z) (2 * τ) * jacobiThetaFourNullTau (2 * τ)) * hL4

/-! ### §20.7(iv) Reduction formulas for products -/

/-- DLMF 20.7.11 (`q² ↔ 2τ`): `θ₁(z|τ)θ₂(z|τ)/θ₁(2z|2τ) = θ₃(z|τ)θ₄(z|τ)/θ₄(2z|2τ) = θ₄(0|2τ)`,
where the denominators do not vanish. Corrected from the printed DLMF formula: nonvanishing
hypotheses added, since with Lean's `x / 0 = 0` the quotients are false at the zeros. -/
@[dlmf 20.7.E11]
theorem jacobiTheta_reduction_two_mul (z τ : ℂ) (hτ : 0 < τ.im) :
    (jacobiThetaOneTau (2 * z) (2 * τ) ≠ 0 →
      jacobiThetaOneTau z τ * jacobiThetaTwoTau z τ / jacobiThetaOneTau (2 * z) (2 * τ) =
        jacobiThetaFourNullTau (2 * τ)) ∧
    (jacobiThetaFourTau (2 * z) (2 * τ) ≠ 0 →
      jacobiThetaThreeTau z τ * jacobiThetaFourTau z τ / jacobiThetaFourTau (2 * z) (2 * τ) =
        jacobiThetaFourNullTau (2 * τ)) := by
  have n4 := (jacobiThetaNullTau_ne_zero (τ := 2 * τ) (by simp; linarith)).2.2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [div_eq_iff h, p20R1_L1 z τ hτ]; ring
  · rw [div_eq_iff h, p20R1_L4 z τ hτ]; ring

/-- DLMF 20.7.12 (`q² ↔ 2τ`): `θ₁(z|2τ)θ₄(z|2τ)/θ₁(z|τ) = θ₂(z|2τ)θ₃(z|2τ)/θ₂(z|τ) = θ₂(0|τ)/2`,
where the denominators do not vanish. Corrected from the printed DLMF formula: nonvanishing
hypotheses added, since with Lean's `x / 0 = 0` the quotients are false at the zeros. -/
@[dlmf 20.7.E12]
theorem jacobiTheta_reduction_two_tau (z τ : ℂ) (hτ : 0 < τ.im) :
    (jacobiThetaOneTau z τ ≠ 0 →
      jacobiThetaOneTau z (2 * τ) * jacobiThetaFourTau z (2 * τ) / jacobiThetaOneTau z τ =
        jacobiThetaTwoNullTau τ / 2) ∧
    (jacobiThetaTwoTau z τ ≠ 0 →
      jacobiThetaTwoTau z (2 * τ) * jacobiThetaThreeTau z (2 * τ) / jacobiThetaTwoTau z τ =
        jacobiThetaTwoNullTau τ / 2) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [div_eq_iff h]; linear_combination p20R1_D1 z τ hτ / 2
  · rw [div_eq_iff h]; linear_combination p20R1_D2 z τ hτ / 2

/-! ### §20.7(v) Watson's identities -/

/-- DLMF 20.7.13: `θ₁(z|τ)θ₁(w|τ) = θ₃(z+w|2τ)θ₂(z-w|2τ) - θ₂(z+w|2τ)θ₃(z-w|2τ)`. -/
@[dlmf 20.7.E13]
theorem jacobiThetaOneTau_mul_watson (z w τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaOneTau z τ * jacobiThetaOneTau w τ =
      jacobiThetaThreeTau (z + w) (2 * τ) * jacobiThetaTwoTau (z - w) (2 * τ) -
        jacobiThetaTwoTau (z + w) (2 * τ) * jacobiThetaThreeTau (z - w) (2 * τ) := by
  exact p20R1_W1 z w τ hτ

/-- DLMF 20.7.14: `θ₃(z|τ)θ₃(w|τ) = θ₃(z+w|2τ)θ₃(z-w|2τ) + θ₂(z+w|2τ)θ₂(z-w|2τ)`. -/
@[dlmf 20.7.E14]
theorem jacobiThetaThreeTau_mul_watson (z w τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau z τ * jacobiThetaThreeTau w τ =
      jacobiThetaThreeTau (z + w) (2 * τ) * jacobiThetaThreeTau (z - w) (2 * τ) +
        jacobiThetaTwoTau (z + w) (2 * τ) * jacobiThetaTwoTau (z - w) (2 * τ) := by
  exact p20R1_W3 z w τ hτ

/-! ### §20.7(vi) Landen transformations -/

/-- DLMF 20.7.15: `A(τ) = 1/θ₄(0|2τ)`. -/
@[dlmf 20.7.E15]
def thetaLandenA (τ : ℂ) : ℂ := 1 / jacobiThetaFourNullTau (2 * τ)

/-- DLMF 20.7.16: `θ₁(2z|2τ) = A θ₁(z|τ) θ₂(z|τ)`. -/
@[dlmf 20.7.E16]
theorem jacobiThetaOneTau_landen (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaOneTau (2 * z) (2 * τ) =
      thetaLandenA τ * jacobiThetaOneTau z τ * jacobiThetaTwoTau z τ := by
  have n4 := (jacobiThetaNullTau_ne_zero (τ := 2 * τ) (by simp; linarith)).2.2
  rw [thetaLandenA, mul_assoc, p20R1_L1 z τ hτ]; field_simp

/-- DLMF 20.7.17: `θ₂(2z|2τ) = A θ₁(π/4 - z|τ) θ₁(π/4 + z|τ)`. -/
@[dlmf 20.7.E17]
theorem jacobiThetaTwoTau_landen (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoTau (2 * z) (2 * τ) =
      thetaLandenA τ * jacobiThetaOneTau (π / 4 - z) τ * jacobiThetaOneTau (π / 4 + z) τ := by
  have n4 := (jacobiThetaNullTau_ne_zero (τ := 2 * τ) (by simp; linarith)).2.2
  rw [thetaLandenA, mul_assoc, p20R1_L2 z τ hτ]; field_simp

/-- DLMF 20.7.18: `θ₃(2z|2τ) = A θ₃(π/4 - z|τ) θ₃(π/4 + z|τ)`. -/
@[dlmf 20.7.E18]
theorem jacobiThetaThreeTau_landen (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau (2 * z) (2 * τ) =
      thetaLandenA τ * jacobiThetaThreeTau (π / 4 - z) τ * jacobiThetaThreeTau (π / 4 + z) τ := by
  have n4 := (jacobiThetaNullTau_ne_zero (τ := 2 * τ) (by simp; linarith)).2.2
  rw [thetaLandenA, mul_assoc, p20R1_L3 z τ hτ]; field_simp

/-- DLMF 20.7.19: `θ₄(2z|2τ) = A θ₃(z|τ) θ₄(z|τ)`. -/
@[dlmf 20.7.E19]
theorem jacobiThetaFourTau_landen (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaFourTau (2 * z) (2 * τ) =
      thetaLandenA τ * jacobiThetaThreeTau z τ * jacobiThetaFourTau z τ := by
  have n4 := (jacobiThetaNullTau_ne_zero (τ := 2 * τ) (by simp; linarith)).2.2
  rw [thetaLandenA, mul_assoc, p20R1_L4 z τ hτ]; field_simp

/-- DLMF 20.7.20: `B(τ) = 1/(θ₃(0|τ) θ₄(0|τ) θ₃(π/4|τ))`. -/
@[dlmf 20.7.E20]
def thetaLandenB (τ : ℂ) : ℂ :=
  1 / (jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ * jacobiThetaThreeTau (π / 4) τ)

/-- DLMF 20.7.21: `θ₁(4z|4τ) = B θ₁(z|τ) θ₁(π/4 - z|τ) θ₁(π/4 + z|τ) θ₂(z|τ)`. -/
@[dlmf 20.7.E21]
theorem jacobiThetaOneTau_landen_four (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaOneTau (4 * z) (4 * τ) = thetaLandenB τ * jacobiThetaOneTau z τ *
      jacobiThetaOneTau (π / 4 - z) τ * jacobiThetaOneTau (π / 4 + z) τ *
        jacobiThetaTwoTau z τ := by
  have h2τ : 0 < (2 * τ).im := by simp; linarith
  have hK : jacobiThetaOneTau (4 * z) (4 * τ) * (jacobiThetaThreeNullTau τ *
      jacobiThetaFourNullTau τ * jacobiThetaThreeTau (π / 4) τ) =
      jacobiThetaOneTau z τ * jacobiThetaOneTau (π / 4 - z) τ * jacobiThetaOneTau (π / 4 + z) τ *
        jacobiThetaTwoTau z τ := by
    have hA := p20R1_L1 (2 * z) (2 * τ) h2τ
    rw [show 2 * (2 * z) = 4 * z by ring, show 2 * (2 * τ) = 4 * τ by ring] at hA
    have hL1 := p20R1_L1 z τ hτ
    have hL2 := p20R1_L2 z τ hτ
    have hL40 := p20R1_L40 τ hτ
    rw [p20R1_three_quarter τ hτ]
    linear_combination (-(jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ)) * hA +
      (jacobiThetaOneTau (2 * z) (2 * τ) * jacobiThetaTwoTau (2 * z) (2 * τ)) * hL40 -
      (jacobiThetaOneTau (π / 4 - z) τ * jacobiThetaOneTau (π / 4 + z) τ) * hL1 -
      (jacobiThetaOneTau (2 * z) (2 * τ) * jacobiThetaFourNullTau (2 * τ)) * hL2
  have hne := one_div_mul_cancel (p20R1_landenB_ne τ hτ)
  rw [thetaLandenB]
  linear_combination (1 / (jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ * jacobiThetaThreeTau (π / 4) τ)) * hK - jacobiThetaOneTau (4 * z) (4 * τ) * hne

/-- DLMF 20.7.22: `θ₂(4z|4τ) = B θ₂(π/8 - z) θ₂(π/8 + z) θ₂(3π/8 - z) θ₂(3π/8 + z)`. -/
@[dlmf 20.7.E22]
theorem jacobiThetaTwoTau_landen_four (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoTau (4 * z) (4 * τ) = thetaLandenB τ * jacobiThetaTwoTau (π / 8 - z) τ *
      jacobiThetaTwoTau (π / 8 + z) τ * jacobiThetaTwoTau (3 * π / 8 - z) τ *
        jacobiThetaTwoTau (3 * π / 8 + z) τ := by
  have h2τ : 0 < (2 * τ).im := by simp; linarith
  have hK : jacobiThetaTwoTau (4 * z) (4 * τ) * (jacobiThetaThreeNullTau τ *
      jacobiThetaFourNullTau τ * jacobiThetaThreeTau (π / 4) τ) =
      jacobiThetaTwoTau (π / 8 - z) τ * jacobiThetaTwoTau (π / 8 + z) τ *
        jacobiThetaTwoTau (3 * π / 8 - z) τ * jacobiThetaTwoTau (3 * π / 8 + z) τ := by
    have hA := p20R1_L2 (2 * z) (2 * τ) h2τ
    rw [show 2 * (2 * z) = 4 * z by ring, show 2 * (2 * τ) = 4 * τ by ring] at hA
    have hx := p20R1_L1 (π / 8 - z) τ hτ
    have hy := p20R1_L1 (π / 8 + z) τ hτ
    rw [show 2 * (π / 8 - z) = π / 4 - 2 * z by ring] at hx
    rw [show 2 * (π / 8 + z) = π / 4 + 2 * z by ring] at hy
    have hL40 := p20R1_L40 τ hτ
    rw [p20R1_three_quarter τ hτ, p20R1_two_eighth_add, p20R1_two_eighth_sub]
    linear_combination (-(jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ)) * hA +
      (jacobiThetaOneTau (π / 4 - 2 * z) (2 * τ) * jacobiThetaOneTau (π / 4 + 2 * z) (2 * τ)) *
        hL40 -
      (jacobiThetaOneTau (π / 8 + z) τ * jacobiThetaTwoTau (π / 8 + z) τ) * hx -
      (jacobiThetaOneTau (π / 4 - 2 * z) (2 * τ) * jacobiThetaFourNullTau (2 * τ)) * hy
  have hne := one_div_mul_cancel (p20R1_landenB_ne τ hτ)
  rw [thetaLandenB]
  linear_combination (1 / (jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ * jacobiThetaThreeTau (π / 4) τ)) * hK - jacobiThetaTwoTau (4 * z) (4 * τ) * hne

/-- DLMF 20.7.23: `θ₃(4z|4τ) = B θ₃(π/8 - z) θ₃(π/8 + z) θ₃(3π/8 - z) θ₃(3π/8 + z)`. -/
@[dlmf 20.7.E23]
theorem jacobiThetaThreeTau_landen_four (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau (4 * z) (4 * τ) = thetaLandenB τ * jacobiThetaThreeTau (π / 8 - z) τ *
      jacobiThetaThreeTau (π / 8 + z) τ * jacobiThetaThreeTau (3 * π / 8 - z) τ *
        jacobiThetaThreeTau (3 * π / 8 + z) τ := by
  have h2τ : 0 < (2 * τ).im := by simp; linarith
  have hK : jacobiThetaThreeTau (4 * z) (4 * τ) * (jacobiThetaThreeNullTau τ *
      jacobiThetaFourNullTau τ * jacobiThetaThreeTau (π / 4) τ) =
      jacobiThetaThreeTau (π / 8 - z) τ * jacobiThetaThreeTau (π / 8 + z) τ *
        jacobiThetaThreeTau (3 * π / 8 - z) τ * jacobiThetaThreeTau (3 * π / 8 + z) τ := by
    have hA := p20R1_L3 (2 * z) (2 * τ) h2τ
    rw [show 2 * (2 * z) = 4 * z by ring, show 2 * (2 * τ) = 4 * τ by ring] at hA
    have hx := p20R1_L4 (π / 8 - z) τ hτ
    have hy := p20R1_L4 (π / 8 + z) τ hτ
    rw [show 2 * (π / 8 - z) = π / 4 - 2 * z by ring, p20R1_four_quarter_sub] at hx
    rw [show 2 * (π / 8 + z) = π / 4 + 2 * z by ring, p20R1_four_quarter_add] at hy
    have hL40 := p20R1_L40 τ hτ
    rw [p20R1_three_quarter τ hτ, p20R1_three_eighth_add, p20R1_three_eighth_sub]
    linear_combination (-(jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ)) * hA +
      (jacobiThetaThreeTau (π / 4 - 2 * z) (2 * τ) * jacobiThetaThreeTau (π / 4 + 2 * z) (2 * τ)) *
        hL40 -
      (jacobiThetaThreeTau (π / 8 + z) τ * jacobiThetaFourTau (π / 8 + z) τ) * hx -
      (jacobiThetaThreeTau (π / 4 + 2 * z) (2 * τ) * jacobiThetaFourNullTau (2 * τ)) * hy
  have hne := one_div_mul_cancel (p20R1_landenB_ne τ hτ)
  rw [thetaLandenB]
  linear_combination (1 / (jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ * jacobiThetaThreeTau (π / 4) τ)) * hK - jacobiThetaThreeTau (4 * z) (4 * τ) * hne

/-- DLMF 20.7.24: `θ₄(4z|4τ) = B θ₄(z|τ) θ₄(π/4 - z|τ) θ₄(π/4 + z|τ) θ₃(z|τ)`. -/
@[dlmf 20.7.E24]
theorem jacobiThetaFourTau_landen_four (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaFourTau (4 * z) (4 * τ) = thetaLandenB τ * jacobiThetaFourTau z τ *
      jacobiThetaFourTau (π / 4 - z) τ * jacobiThetaFourTau (π / 4 + z) τ *
        jacobiThetaThreeTau z τ := by
  have h2τ : 0 < (2 * τ).im := by simp; linarith
  have hK : jacobiThetaFourTau (4 * z) (4 * τ) * (jacobiThetaThreeNullTau τ *
      jacobiThetaFourNullTau τ * jacobiThetaThreeTau (π / 4) τ) =
      jacobiThetaFourTau z τ * jacobiThetaFourTau (π / 4 - z) τ *
        jacobiThetaFourTau (π / 4 + z) τ * jacobiThetaThreeTau z τ := by
    have hA := p20R1_L4 (2 * z) (2 * τ) h2τ
    rw [show 2 * (2 * z) = 4 * z by ring, show 2 * (2 * τ) = 4 * τ by ring] at hA
    have hL4 := p20R1_L4 z τ hτ
    have hL3 := p20R1_L3 z τ hτ
    have hL40 := p20R1_L40 τ hτ
    rw [p20R1_three_quarter τ hτ, p20R1_four_quarter_sub, p20R1_four_quarter_add]
    linear_combination (-(jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ)) * hA +
      (jacobiThetaThreeTau (2 * z) (2 * τ) * jacobiThetaFourTau (2 * z) (2 * τ)) * hL40 -
      (jacobiThetaThreeTau (π / 4 - z) τ * jacobiThetaThreeTau (π / 4 + z) τ) * hL4 -
      (jacobiThetaFourTau (2 * z) (2 * τ) * jacobiThetaFourNullTau (2 * τ)) * hL3
  have hne := one_div_mul_cancel (p20R1_landenB_ne τ hτ)
  rw [thetaLandenB]
  linear_combination (1 / (jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ * jacobiThetaThreeTau (π / 4) τ)) * hK - jacobiThetaFourTau (4 * z) (4 * τ) * hne

/-! ### §20.7(viii) Transformations of lattice parameter -/

/-- `e^{iπ m(m+1)} = 1` for integer `m`: `m(m+1)` is even. -/
lemma th20_exp_pi_mul_I_mul_succ (m : ℤ) : cexp (π * I * (m * (m + 1) : ℤ)) = 1 := by
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self m
  rw [hk, ← exp_int_mul_two_pi_mul_I k]
  congr 1; push_cast; ring

/-- DLMF 20.7.28: `θ₃(z|τ + 1) = θ₄(z|τ)`. -/
@[dlmf 20.7.E28]
theorem jacobiThetaThreeTau_add_one (z τ : ℂ) :
    jacobiThetaThreeTau z (τ + 1) = jacobiThetaFourTau z τ := by
  rw [jacobiThetaThreeTau_eq_tsum, jacobiThetaFourTau_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [th20_neg_one_zpow, ← exp_add, exp_eq_exp_iff_exists_int]
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self (n - 1)
  refine ⟨k, ?_⟩
  have hk2 : (n - 1) * n = k + k := by rw [← hk]; ring
  have hk' : ((n : ℂ) - 1) * n = 2 * k := by
    have := congrArg (fun x : ℤ => (x : ℂ)) hk2
    push_cast at this
    linear_combination this
  linear_combination π * I * hk'

/-- DLMF 20.7.29: `θ₄(z|τ + 1) = θ₃(z|τ)`. -/
@[dlmf 20.7.E29]
theorem jacobiThetaFourTau_add_one (z τ : ℂ) :
    jacobiThetaFourTau z (τ + 1) = jacobiThetaThreeTau z τ := by
  rw [jacobiThetaFourTau, jacobiThetaThreeTau_add_one, jacobiThetaFourTau,
    show z + π / 2 + π / 2 = z + π by ring, jacobiThetaThreeTau_add_pi]

/-- `cexp(iπ(τ+1))^{n(n+1)} = cexp(iπτ)^{n(n+1)}`. -/
lemma th20_nome_add_one_zpow (τ : ℂ) (n : ℤ) :
    cexp (π * I * (τ + 1)) ^ (n * (n + 1)) = cexp (π * I * τ) ^ (n * (n + 1)) := by
  rw [th20_exp_zpow, th20_exp_zpow, show ((n * (n + 1) : ℤ) : ℂ) * (π * I * (τ + 1)) =
    ((n * (n + 1) : ℤ) : ℂ) * (π * I * τ) + π * I * ((n * (n + 1) : ℤ) : ℂ) by ring, exp_add,
    th20_exp_pi_mul_I_mul_succ, mul_one]

/-- DLMF 20.7.27: `θ₂(z|τ + 1) = e^{iπ/4} θ₂(z|τ)`. -/
@[dlmf 20.7.E27]
theorem jacobiThetaTwoTau_add_one (z τ : ℂ) :
    jacobiThetaTwoTau z (τ + 1) = cexp (π * I / 4) * jacobiThetaTwoTau z τ := by
  rw [jacobiThetaTwoTau_eq_tsum, jacobiThetaTwoTau_eq_tsum]
  simp_rw [th20_nome_add_one_zpow]
  rw [← mul_assoc, ← exp_add]
  congr 2; ring

/-- DLMF 20.7.26: `θ₁(z|τ + 1) = e^{iπ/4} θ₁(z|τ)`. -/
@[dlmf 20.7.E26]
theorem jacobiThetaOneTau_add_one (z τ : ℂ) :
    jacobiThetaOneTau z (τ + 1) = cexp (π * I / 4) * jacobiThetaOneTau z τ := by
  rw [jacobiThetaOneTau, jacobiThetaTwoTau_add_one, jacobiThetaOneTau]
  ring

/-- `θ₁(x - π/2|τ) = -θ₂(x|τ)` (helper). -/
lemma p3t_one_sub_half (x τ : ℂ) : jacobiThetaOneTau (x - π / 2) τ = -jacobiThetaTwoTau x τ := by
  rw [jacobiThetaOneTau, sub_add_cancel]

/-- `θ₂(x - π/2|τ) = θ₁(x|τ)` (helper). -/
lemma p3t_two_sub_half (x τ : ℂ) : jacobiThetaTwoTau (x - π / 2) τ = jacobiThetaOneTau x τ := by
  have h := p20R1_one_add_half (x - π / 2) τ
  rw [sub_add_cancel] at h
  exact h.symm

/-- `θ₃(x - π/2|τ) = θ₄(x|τ)` (helper). -/
lemma p3t_three_sub_half (x τ : ℂ) :
    jacobiThetaThreeTau (x - π / 2) τ = jacobiThetaFourTau x τ := by
  rw [jacobiThetaFourTau, show x + π / 2 = (x - π / 2) + π by ring, jacobiThetaThreeTau_add_pi]

/-- Mixed product `θ₂(0)θ₃(0) θ₁(u+v)θ₄(u-v) = θ₁θ₄(u) θ₂θ₃(v) + θ₂θ₃(u) θ₁θ₄(v)` (helper). -/
theorem p3t_mixed14 (u v τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoNullTau τ * jacobiThetaThreeNullTau τ *
        (jacobiThetaOneTau (u + v) τ * jacobiThetaFourTau (u - v) τ) =
      jacobiThetaOneTau u τ * jacobiThetaFourTau u τ *
          (jacobiThetaTwoTau v τ * jacobiThetaThreeTau v τ) +
        jacobiThetaTwoTau u τ * jacobiThetaThreeTau u τ *
          (jacobiThetaOneTau v τ * jacobiThetaFourTau v τ) := by
  have hσ : 0 < (τ / 2).im := by simp; linarith
  have h2 : 2 * (τ / 2) = τ := by ring
  have k1 := p20R1_W1 u (v - π / 2) (τ / 2) hσ
  have k2 := p20R1_W1 v (u - π / 2) (τ / 2) hσ
  rw [h2, p3t_one_sub_half, show u + (v - π / 2) = (u + v) - π / 2 by ring,
    show u - (v - π / 2) = (u - v) + π / 2 by ring, p3t_three_sub_half,
    p20R1_two_add_half, p3t_two_sub_half, p20R1_three_add_half] at k1
  rw [h2, p3t_one_sub_half, show v + (u - π / 2) = (u + v) - π / 2 by ring,
    show v - (u - π / 2) = -(u - v) + π / 2 by ring, p3t_three_sub_half,
    p20R1_two_add_half, p3t_two_sub_half, p20R1_three_add_half,
    jacobiThetaOneTau_neg, jacobiThetaFourTau_neg] at k2
  have d1u := p20R1_D1 u (τ / 2) hσ
  have d1v := p20R1_D1 v (τ / 2) hσ
  have d2u := p20R1_D2 u (τ / 2) hσ
  have d2v := p20R1_D2 v (τ / 2) hσ
  have d20 := p20R1_D2 0 (τ / 2) hσ
  rw [h2] at d1u d1v d2u d2v d20
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau] at d1u d1v d2u d2v d20 ⊢
  set g := jacobiThetaTwoTau 0 (τ / 2)
  linear_combination (1 / 2 * (jacobiThetaOneTau (u + v) τ * jacobiThetaFourTau (u - v) τ)) * d20
    + g ^ 2 / 4 * k1 + g ^ 2 / 4 * k2
    - (1 / 2 * (jacobiThetaTwoTau v τ * jacobiThetaThreeTau v τ)) * d1u
    - (jacobiThetaOneTau u (τ / 2) * g / 4) * d2v
    - (1 / 2 * (jacobiThetaOneTau v τ * jacobiThetaFourTau v τ)) * d2u
    - (jacobiThetaTwoTau u (τ / 2) * g / 4) * d1v

/-- Mixed product `θ₂(0)θ₄(0) θ₂(u+v)θ₄(u-v) = θ₂θ₄(u) θ₂θ₄(v) - θ₁θ₃(u) θ₁θ₃(v)` (helper). -/
theorem p3t_mixed24 (u v τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoNullTau τ * jacobiThetaFourNullTau τ *
        (jacobiThetaTwoTau (u + v) τ * jacobiThetaFourTau (u - v) τ) =
      jacobiThetaTwoTau u τ * jacobiThetaFourTau u τ *
          (jacobiThetaTwoTau v τ * jacobiThetaFourTau v τ) -
        jacobiThetaOneTau u τ * jacobiThetaThreeTau u τ *
          (jacobiThetaOneTau v τ * jacobiThetaThreeTau v τ) := by
  have hτ1 : 0 < (τ + 1).im := by simpa using hτ
  have h := p3t_mixed14 (u + π / 2) v (τ + 1) hτ1
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau,
    jacobiThetaOneTau_add_one, jacobiThetaTwoTau_add_one, jacobiThetaThreeTau_add_one,
    jacobiThetaFourTau_add_one] at h ⊢
  rw [show u + π / 2 + v = (u + v) + π / 2 by ring, show u + π / 2 - v = (u - v) + π / 2 by ring,
    p20R1_one_add_half, p20R1_two_add_half, p20R1_three_add_half, p20R1_four_add_half,
    p20R1_one_add_half, p20R1_three_add_half] at h
  have hε : cexp (π * I / 4) ^ 2 ≠ 0 := pow_ne_zero _ (exp_ne_zero _)
  apply mul_left_cancel₀ hε
  linear_combination h

/-- The derivative at  of an even differentiable function vanishes (helper). -/
theorem p3t_deriv_even {f : ℂ → ℂ} (hf : Differentiable ℂ f) (he : ∀ z, f (-z) = f z) :
    deriv f 0 = 0 := by
  have h1 : HasDerivAt f (deriv f 0) (-0) := by rw [neg_zero]; exact (hf 0).hasDerivAt
  have h2 := h1.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
  have h3 : (f ∘ fun x => -x) = f := funext fun z => he z
  rw [h3] at h2
  have := h2.unique (hf 0).hasDerivAt
  linear_combination -this / 2

/-! ### §20.7(vii) Derivatives of ratios of theta functions -/

/-- DLMF 20.7.25: `d/dz (θ₂(z|τ)/θ₄(z|τ)) = -θ₃²(0|τ) θ₁(z|τ) θ₃(z|τ)/θ₄²(z|τ)` where
`θ₄(z|τ) ≠ 0`. Corrected from the printed DLMF formula: the hypothesis `θ₄(z|τ) ≠ 0` is added,
since at a zero of `θ₄` the quotient has a pole (Lean's `x / 0 = 0`). -/
@[dlmf 20.7.E25]
theorem hasDerivAt_jacobiThetaTwoTau_div_four {z τ : ℂ} (hτ : 0 < τ.im)
    (hz : jacobiThetaFourTau z τ ≠ 0) :
    HasDerivAt (fun w => jacobiThetaTwoTau w τ / jacobiThetaFourTau w τ)
      (-(jacobiThetaThreeNullTau τ ^ 2 * jacobiThetaOneTau z τ * jacobiThetaThreeTau z τ) /
        jacobiThetaFourTau z τ ^ 2) z := by
  have hd : ∀ j, ∀ x : ℂ, HasDerivAt (fun w => jacobiThetaTau j w τ)
      (deriv (fun w => jacobiThetaTau j w τ) x) x :=
    fun j x => ((differentiable_jacobiThetaTau j hτ) x).hasDerivAt
  have h2 := hd 2 z
  have h4 := hd 4 z
  simp only [jacobiThetaTau] at h2 h4
  set a := deriv (fun w => jacobiThetaTwoTau w τ) z
  set b := deriv (fun w => jacobiThetaFourTau w τ) z
  -- differentiate the mixed identity in `v` at `0`
  have hL : HasDerivAt (fun v => jacobiThetaTwoNullTau τ * jacobiThetaFourNullTau τ *
      (jacobiThetaTwoTau (z + v) τ * jacobiThetaFourTau (z - v) τ))
      (jacobiThetaTwoNullTau τ * jacobiThetaFourNullTau τ *
        (a * jacobiThetaFourTau z τ + jacobiThetaTwoTau z τ * -b)) 0 := by
    have h2' : HasDerivAt (fun w => jacobiThetaTwoTau w τ) a (z + 0) := by rwa [add_zero]
    have h4' : HasDerivAt (fun w => jacobiThetaFourTau w τ) b (z - 0) := by rwa [sub_zero]
    have := ((h2'.comp_const_add z 0).mul (h4'.comp_const_sub z 0)).const_mul
      (jacobiThetaTwoNullTau τ * jacobiThetaFourNullTau τ)
    simp only [add_zero, sub_zero] at this
    exact this
  have d1 := hd 1 0
  have d2 := hd 2 0
  have d3 := hd 3 0
  have d4 := hd 4 0
  simp only [jacobiThetaTau] at d1 d2 d3 d4
  have e2 := p3t_deriv_even (differentiable_jacobiThetaTau 2 hτ)
    (fun w => jacobiThetaTwoTau_neg w τ)
  have e3 := p3t_deriv_even (differentiable_jacobiThetaTau 3 hτ)
    (fun w => jacobiThetaThreeTau_neg w τ)
  have e4 := p3t_deriv_even (differentiable_jacobiThetaTau 4 hτ)
    (fun w => jacobiThetaFourTau_neg w τ)
  simp only [jacobiThetaTau] at e2 e3 e4
  rw [e2] at d2; rw [e3] at d3; rw [e4] at d4
  have e1 := jacobiThetaOneDerivNullTau_eq_mul hτ
  simp only [jacobiThetaOneDerivNullTau] at e1
  rw [e1] at d1
  have hR := ((d2.mul d4).const_mul (jacobiThetaTwoTau z τ * jacobiThetaFourTau z τ)).sub
    ((d1.mul d3).const_mul (jacobiThetaOneTau z τ * jacobiThetaThreeTau z τ))
  have hLR : HasDerivAt (fun v => jacobiThetaTwoNullTau τ * jacobiThetaFourNullTau τ *
      (jacobiThetaTwoTau (z + v) τ * jacobiThetaFourTau (z - v) τ))
      (-(jacobiThetaOneTau z τ * jacobiThetaThreeTau z τ *
        (jacobiThetaTwoNullTau τ * jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ *
          jacobiThetaThreeTau 0 τ))) 0 := by
    convert hR using 1
    swap
    · simp only [p20R1_one_zero]; ring
    funext v
    exact p3t_mixed24 z v τ hτ
  have heq := hL.unique hLR
  obtain ⟨n2, n3, n4⟩ := jacobiThetaNullTau_ne_zero hτ
  have hW : a * jacobiThetaFourTau z τ - jacobiThetaTwoTau z τ * b =
      -(jacobiThetaThreeNullTau τ ^ 2 * jacobiThetaOneTau z τ * jacobiThetaThreeTau z τ) := by
    apply mul_left_cancel₀ (mul_ne_zero n2 n4)
    simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau] at heq ⊢
    linear_combination heq
  have := h2.div h4 hz
  rwa [hW] at this

/-! ### §20.7(viii) Transformations of lattice parameter (continued) -/

/-- DLMF 20.7.32: `(-iτ)^{1/2} θ₃(z|τ) = exp(iτ'z²/π) θ₃(zτ'|τ')`, `τ' = -1/τ`, principal
square root, `Im τ > 0`. -/
@[dlmf 20.7.E32]
theorem jacobiThetaThreeTau_neg_inv {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    (-I * τ) ^ (1 / 2 : ℂ) * jacobiThetaThreeTau z τ =
      cexp (I * (-1 / τ) * z ^ 2 / π) * jacobiThetaThreeTau (z * (-1 / τ)) (-1 / τ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hne : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ0))
  rw [jacobiThetaThreeTau, jacobiTheta₂_functional_equation, jacobiThetaThreeTau,
    show z * (-1 / τ) / π = -(z / π / τ) by field_simp, jacobiTheta₂_neg_left]
  field_simp

/-- DLMF 20.7.33: `(-iτ)^{1/2} θ₄(z|τ) = exp(iτ'z²/π) θ₂(zτ'|τ')`, `τ' = -1/τ`, `Im τ > 0`. -/
@[dlmf 20.7.E33]
theorem jacobiThetaFourTau_neg_inv {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    (-I * τ) ^ (1 / 2 : ℂ) * jacobiThetaFourTau z τ =
      cexp (I * (-1 / τ) * z ^ 2 / π) * jacobiThetaTwoTau (z * (-1 / τ)) (-1 / τ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  rw [jacobiThetaFourTau, jacobiThetaThreeTau_neg_inv hτ,
    (jacobiThetaTwoTau_half_periods (z * (-1 / τ)) (-1 / τ)).2.1, thetaMultiplierM,
    show (z + π / 2) * (-1 / τ) = z * (-1 / τ) + π * (-1 / τ) / 2 by ring, ← mul_assoc, ← exp_add]
  congr 2
  field_simp [pi_ne_zero']
  ring

/-- DLMF 20.7.31: `(-iτ)^{1/2} θ₂(z|τ) = exp(iτ'z²/π) θ₄(zτ'|τ')`, `τ' = -1/τ`, `Im τ > 0`. -/
@[dlmf 20.7.E31]
theorem jacobiThetaTwoTau_neg_inv {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    (-I * τ) ^ (1 / 2 : ℂ) * jacobiThetaTwoTau z τ =
      cexp (I * (-1 / τ) * z ^ 2 / π) * jacobiThetaFourTau (z * (-1 / τ)) (-1 / τ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  rw [jacobiThetaTwoTau, mul_left_comm, jacobiThetaThreeTau_neg_inv hτ,
    show (z + π * τ / 2) * (-1 / τ) = z * (-1 / τ) - π / 2 by field_simp; ring,
    jacobiThetaFourTau, ← jacobiThetaThreeTau_add_pi (z * (-1 / τ) - π / 2),
    show z * (-1 / τ) - π / 2 + π = z * (-1 / τ) + π / 2 by ring, ← mul_assoc, ← exp_add]
  congr 2
  field_simp [pi_ne_zero']
  ring

/-- DLMF 20.7.30: `(-iτ)^{1/2} θ₁(z|τ) = -i exp(iτ'z²/π) θ₁(zτ'|τ')`, `τ' = -1/τ`, `Im τ > 0`. -/
@[dlmf 20.7.E30]
theorem jacobiThetaOneTau_neg_inv {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    (-I * τ) ^ (1 / 2 : ℂ) * jacobiThetaOneTau z τ =
      -I * cexp (I * (-1 / τ) * z ^ 2 / π) * jacobiThetaOneTau (z * (-1 / τ)) (-1 / τ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  rw [jacobiThetaOneTau, mul_neg, jacobiThetaTwoTau_neg_inv hτ,
    (jacobiThetaOneTau_half_periods (z * (-1 / τ)) (-1 / τ)).2.1, thetaMultiplierM,
    show (z + π / 2) * (-1 / τ) = z * (-1 / τ) + π * (-1 / τ) / 2 by ring]
  have h : cexp (I * (-1 / τ) * (z + π / 2) ^ 2 / π) =
      cexp (I * (-1 / τ) * z ^ 2 / π) * cexp (I * (z * (-1 / τ)) + π * I * (-1 / τ) / 4) := by
    rw [← exp_add]; congr 1; field_simp [pi_ne_zero']; ring
  rw [h]
  ring_nf
  rw [I_sq]
  ring

/-- Multipliability of `1 - c y^{k+1}`-type products (helper). -/
lemma p20R1_hasProd_one_sub {f : ℕ → ℂ} {ρ : ℝ} (hρ : ρ < 1) (hf : ∀ k, ‖f k‖ ≤ ρ ^ (k + 1)) :
    HasProd (fun k => 1 - f k) (∏' k, (1 - f k)) := by
  have h0 : 0 ≤ ρ := by have := hf 0; rw [pow_one] at this; exact (norm_nonneg _).trans this
  have hs : Summable (fun k => ‖f k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hf
      ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one h0 hρ))
  exact (multipliable_one_sub_of_summable hs).hasProd

/-- The product identity `θ₂(0|τ+½) η(2τ) = 2 e^{iπ/8} η(τ) η(4τ)` (helper for 20.7.34). -/
lemma p20R1_two_null_half_eta {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiThetaTwoNullTau (τ + 1 / 2) * ModularForm.eta (2 * τ) =
      2 * cexp (π * I / 8) * (ModularForm.eta τ * ModularForm.eta (4 * τ)) := by
  have hτ' : 0 < (τ + 1 / 2).im := by simpa using hτ
  obtain ⟨-, h2⟩ := jacobiThetaTwoTau_hasProd 0 hτ'
  set p := cexp (2 * π * I * τ) with hp
  have hpn : ‖p‖ < 1 := by
    rw [hp, norm_exp]
    have : (2 * π * I * τ).re = -(2 * π * τ.im) := by simp
    rw [this, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  have hp0 : 0 ≤ ‖p‖ := norm_nonneg _
  have hE2 : cexp (π * I * (τ + 1 / 2)) ^ 2 = -p := by
    rw [← exp_nat_mul, hp, show ((2 : ℕ) : ℂ) * (π * I * (τ + 1 / 2)) = 2 * π * I * τ + π * I by
      push_cast; ring, exp_add, exp_pi_mul_I]; ring
  have pw : ∀ (m k : ℕ), 1 ≤ m → ‖p ^ (m * (k + 1))‖ ≤ ‖p‖ ^ (k + 1) := fun m k hm => by
    rw [norm_pow]; exact pow_le_pow_of_le_one hp0 hpn.le (by nlinarith)
  have pw' : ∀ k : ℕ, ‖p ^ (2 * k + 1)‖ ≤ ‖p‖ ^ (k + 1) := fun k => by
    rw [norm_pow]; exact pow_le_pow_of_le_one hp0 hpn.le (by omega)
  have hA := p20R1_hasProd_one_sub hpn (f := fun k => p ^ (k + 1)) (fun k => by simp)
  have hB := p20R1_hasProd_one_sub hpn (f := fun k => p ^ (2 * (k + 1))) (fun k => pw 2 k (by norm_num))
  have hC := p20R1_hasProd_one_sub hpn (f := fun k => p ^ (4 * (k + 1))) (fun k => pw 4 k (by norm_num))
  have hBp := p20R1_hasProd_one_sub hpn (f := fun k => -p ^ (2 * (k + 1))) (fun k => by
    rw [norm_neg]; exact pw 2 k (by norm_num))
  have hO := p20R1_hasProd_one_sub hpn (f := fun k => p ^ (2 * k + 1)) pw'
  have hD := p20R1_hasProd_one_sub hpn (f := fun k => -(-p) ^ (k + 1)) (fun k => by
    rw [norm_neg, norm_pow, norm_neg])
  simp only [sub_neg_eq_add] at hBp hD
  set A := ∏' k : ℕ, (1 - p ^ (k + 1))
  set B := ∏' k : ℕ, (1 - p ^ (2 * (k + 1)))
  set C := ∏' k : ℕ, (1 - p ^ (4 * (k + 1)))
  set Bp := ∏' k : ℕ, (1 + p ^ (2 * (k + 1)))
  set O := ∏' k : ℕ, (1 - p ^ (2 * k + 1))
  set D := ∏' k : ℕ, (1 + (-p) ^ (k + 1))
  have hAs : A = O * B := by
    refine hA.unique (HasProd.even_mul_odd hO ?_)
    convert hB using 3
  have hDs : D = O * Bp := by
    refine hD.unique (HasProd.even_mul_odd ?_ ?_)
    · convert hO using 2 with k; rw [neg_pow, pow_succ, pow_mul]; norm_num; ring
    · convert hBp using 2 with k
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, neg_pow, pow_mul, pow_mul]; norm_num
  have hCs : C = B * Bp := by
    refine hC.unique ?_
    convert hB.mul hBp using 2 with k
    rw [show 4 * (k + 1) = 2 * (k + 1) + 2 * (k + 1) by ring, pow_add]; ring
  have hfac : ∀ k : ℕ, (1 - cexp (π * I * (τ + 1 / 2)) ^ (2 * (k + 1))) *
      (1 + 2 * cexp (π * I * (τ + 1 / 2)) ^ (2 * (k + 1)) * cos (2 * 0) +
        cexp (π * I * (τ + 1 / 2)) ^ (4 * (k + 1))) =
      (1 - p ^ (2 * (k + 1))) * (1 + (-p) ^ (k + 1)) := fun k => by
    rw [pow_mul, show 4 * (k + 1) = 2 * (2 * (k + 1)) by ring, pow_mul, hE2, mul_zero, cos_zero]
    have hy2 : ((-p) ^ (k + 1)) ^ 2 = p ^ (2 * (k + 1)) := by
      rw [← pow_mul, mul_comm, pow_mul, neg_sq, ← pow_mul]
    rw [show (-p) ^ (2 * (k + 1)) = ((-p) ^ (k + 1)) ^ 2 by rw [← pow_mul, mul_comm]]
    linear_combination (-(1 + (-p) ^ (k + 1))) * hy2
  have h2' : jacobiThetaTwoNullTau (τ + 1 / 2) = 2 * cexp (π * I * (τ + 1 / 2) / 4) * (B * D) := by
    rw [jacobiThetaTwoNullTau, h2, tprod_congr hfac, (hB.mul hD).tprod_eq, cos_zero, mul_one]
  have heta : ∀ (m : ℕ) (T : ℂ), cexp (2 * π * I * T) = p ^ m →
      ModularForm.eta T = cexp (2 * π * I * T / 24) * ∏' k : ℕ, (1 - p ^ (m * (k + 1))) := by
    intro m T hT
    rw [ModularForm.eta]
    simp only [ModularForm.eta_q_eq_pow, hT, ← pow_mul]
    rfl
  have e1 := heta 1 τ (by rw [pow_one])
  have e2 := heta 2 (2 * τ) (by rw [hp, ← exp_nat_mul]; congr 1; push_cast; ring)
  have e4 := heta 4 (4 * τ) (by rw [hp, ← exp_nat_mul]; congr 1; push_cast; ring)
  simp only [one_mul] at e1
  rw [h2', e1, e2, e4, hDs, show (∏' k : ℕ, (1 - p ^ (k + 1))) = A from rfl, hAs,
    show (∏' k : ℕ, (1 - p ^ (4 * (k + 1)))) = C from rfl, hCs]
  have hx : cexp (π * I * (τ + 1 / 2) / 4) * cexp (2 * π * I * (2 * τ) / 24) =
      cexp (π * I / 8) * (cexp (2 * π * I * τ / 24) * cexp (2 * π * I * (4 * τ) / 24)) := by
    simp only [← exp_add]; congr 1; ring
  linear_combination (2 * (B * (O * Bp)) * B) * hx

/-- The common value `θ₂(0|τ+½)/(2e^{iπ/4})` of the two quotients in 20.7.34 (helper). -/
lemma p20R1_iq_ratio (z τ : ℂ) (hτ : 0 < τ.im) :
    (jacobiThetaOneTau z (τ + 1 / 2) ≠ 0 →
      jacobiThetaOneTau z (2 * τ) * jacobiThetaThreeTau z (2 * τ) /
        jacobiThetaOneTau z (τ + 1 / 2) = jacobiThetaTwoNullTau (τ + 1 / 2) / (2 * cexp (π * I / 4))) ∧
    (jacobiThetaTwoTau z (τ + 1 / 2) ≠ 0 →
      jacobiThetaTwoTau z (2 * τ) * jacobiThetaFourTau z (2 * τ) /
        jacobiThetaTwoTau z (τ + 1 / 2) = jacobiThetaTwoNullTau (τ + 1 / 2) / (2 * cexp (π * I / 4))) := by
  have hτ' : 0 < (τ + 1 / 2).im := by simpa using hτ
  have h2 : 2 * (τ + 1 / 2) = 2 * τ + 1 := by ring
  have hD1 := p20R1_D1 z (τ + 1 / 2) hτ'
  have hD2 := p20R1_D2 z (τ + 1 / 2) hτ'
  rw [h2, jacobiThetaOneTau_add_one, jacobiThetaFourTau_add_one] at hD1
  rw [h2, jacobiThetaTwoTau_add_one, jacobiThetaThreeTau_add_one] at hD2
  have hne : cexp (π * I / 4) ≠ 0 := exp_ne_zero _
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [div_eq_div_iff h (mul_ne_zero two_ne_zero hne)]
    linear_combination hD1
  · rw [div_eq_div_iff h (mul_ne_zero two_ne_zero hne)]
    linear_combination hD2

/-- `θ₂(0|τ+½)/(2e^{iπ/4}) = e^{-iπ/8} η(τ)η(4τ)/η(2τ)` (helper). -/
lemma p20R1_ratio_eta {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiThetaTwoNullTau (τ + 1 / 2) / (2 * cexp (π * I / 4)) =
      cexp (-(π * I / 8)) * (ModularForm.eta τ * ModularForm.eta (4 * τ) / ModularForm.eta (2 * τ)) := by
  have key := p20R1_two_null_half_eta hτ
  have hη2 : ModularForm.eta (2 * τ) ≠ 0 :=
    ModularForm.eta_ne_zero (by show 0 < (2 * τ).im; simp; linarith)
  have hee : cexp (π * I / 4) = cexp (π * I / 8) * cexp (π * I / 8) := by
    rw [← exp_add]; congr 1; ring
  have hinv : cexp (-(π * I / 8)) * cexp (π * I / 8) = 1 := by rw [← exp_add]; simp
  have hne : cexp (π * I / 4) ≠ 0 := exp_ne_zero _
  rw [div_eq_iff (mul_ne_zero two_ne_zero hne), hee]
  linear_combination (ModularForm.eta (2 * τ))⁻¹ * key -
    jacobiThetaTwoNullTau (τ + 1 / 2) * mul_inv_cancel₀ hη2 -
    2 * cexp (π * I / 8) * (ModularForm.eta τ * ModularForm.eta (4 * τ)) *
      (ModularForm.eta (2 * τ))⁻¹ * hinv

/-- DLMF 20.7.34 (`q² ↔ 2τ`, `iq ↔ τ + 1/2`), **corrected**: the squared, branch-free form
`(θ₁(z|2τ)θ₃(z|2τ)/θ₁(z|τ+½))² = (θ₂(z|2τ)θ₄(z|2τ)/θ₂(z|τ+½))² = e^{-iπ/4} θ₂(0|2τ)θ₄(0|2τ)/2`
for all `τ` with `Im τ > 0` and nonvanishing denominators.
Corrected from the printed DLMF formula: with principal `√` and `i^{-1/4} = e^{-iπ/8}` the
printed identity fails by a sign for some `τ` (e.g. `τ = -2.19 + 1.29i`); squaring removes the
branch (see also `jacobiTheta_reduction_iq_eta` and `jacobiTheta_reduction_iq_rectangular`).
The nonvanishing hypotheses are added because Lean's `x / 0 = 0` makes the quotients false at
the zeros. -/
@[dlmf 20.7.E34 "corrected: squared form; printed principal-root form only up to sign"]
theorem jacobiTheta_reduction_iq_sq (z τ : ℂ) (hτ : 0 < τ.im) :
    (jacobiThetaOneTau z (τ + 1 / 2) ≠ 0 →
      (jacobiThetaOneTau z (2 * τ) * jacobiThetaThreeTau z (2 * τ) /
        jacobiThetaOneTau z (τ + 1 / 2)) ^ 2 =
        cexp (-(π * I / 4)) *
          (jacobiThetaTwoNullTau (2 * τ) * jacobiThetaFourNullTau (2 * τ) / 2)) ∧
    (jacobiThetaTwoTau z (τ + 1 / 2) ≠ 0 →
      (jacobiThetaTwoTau z (2 * τ) * jacobiThetaFourTau z (2 * τ) /
        jacobiThetaTwoTau z (τ + 1 / 2)) ^ 2 =
        cexp (-(π * I / 4)) *
          (jacobiThetaTwoNullTau (2 * τ) * jacobiThetaFourNullTau (2 * τ) / 2)) := by
  have hτ' : 0 < (τ + 1 / 2).im := by simpa using hτ
  have h2 : 2 * (τ + 1 / 2) = 2 * τ + 1 := by ring
  have hD1 := p20R1_D1 z (τ + 1 / 2) hτ'
  have hD2 := p20R1_D2 z (τ + 1 / 2) hτ'
  have hN := p20R1_D2 0 (τ + 1 / 2) hτ'
  rw [h2, jacobiThetaOneTau_add_one, jacobiThetaFourTau_add_one] at hD1
  rw [h2, jacobiThetaTwoTau_add_one, jacobiThetaThreeTau_add_one] at hD2 hN
  set e := cexp (π * I / 4) with he
  have hne : e ≠ 0 := exp_ne_zero _
  have hinv : cexp (-(π * I / 4)) = e⁻¹ := by rw [exp_neg]
  rw [hinv]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hR : jacobiThetaOneTau z (2 * τ) * jacobiThetaThreeTau z (2 * τ) /
        jacobiThetaOneTau z (τ + 1 / 2) = jacobiThetaTwoNullTau (τ + 1 / 2) / (2 * e) := by
      rw [div_eq_div_iff h (mul_ne_zero two_ne_zero hne)]
      linear_combination hD1
    rw [hR, div_pow, div_eq_iff (pow_ne_zero 2 (mul_ne_zero two_ne_zero hne))]
    linear_combination -hN - 2 * e * jacobiThetaTwoNullTau (2 * τ) *
      jacobiThetaFourNullTau (2 * τ) * inv_mul_cancel₀ hne
  · have hR : jacobiThetaTwoTau z (2 * τ) * jacobiThetaFourTau z (2 * τ) /
        jacobiThetaTwoTau z (τ + 1 / 2) = jacobiThetaTwoNullTau (τ + 1 / 2) / (2 * e) := by
      rw [div_eq_div_iff h (mul_ne_zero two_ne_zero hne)]
      linear_combination hD2
    rw [hR, div_pow, div_eq_iff (pow_ne_zero 2 (mul_ne_zero two_ne_zero hne))]
    linear_combination -hN - 2 * e * jacobiThetaTwoNullTau (2 * τ) *
      jacobiThetaFourNullTau (2 * τ) * inv_mul_cancel₀ hne

/-- On the imaginary axis Dedekind's `η` is a positive real (helper for 20.7.34). -/
lemma p20R1_eta_imag {s : ℝ} (hs : 0 < s) :
    ∃ r : ℝ, 0 < r ∧ ModularForm.eta (I * s) = r := by
  set x : ℝ := Real.exp (-(2 * π * s)) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by rw [hx, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  have hq : cexp (2 * π * I * (I * s)) = (x : ℂ) := by
    rw [hx, ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  have hxn : ‖(x : ℂ)‖ < 1 := by rw [norm_real, Real.norm_of_nonneg hx0.le]; exact hx1
  have hP := (ModularForm.multipliable_one_sub_pow hxn).hasProd
  set P := ∏' n : ℕ, (1 - (x : ℂ) ^ (n + 1)) with hPdef
  have hS : IsClosed {w : ℂ | w.im = 0 ∧ 0 ≤ w.re} :=
    (isClosed_eq continuous_im continuous_const).inter (isClosed_le continuous_const continuous_re)
  have hmem : P ∈ {w : ℂ | w.im = 0 ∧ 0 ≤ w.re} := by
    refine hS.mem_of_tendsto hP (Eventually.of_forall fun F => ?_)
    have : ∏ n ∈ F, (1 - (x : ℂ) ^ (n + 1)) = ((∏ n ∈ F, (1 - x ^ (n + 1)) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [Set.mem_ofPred_eq, this, ofReal_im, ofReal_re]
    exact ⟨rfl, Finset.prod_nonneg fun n _ => by
      have : x ^ (n + 1) < 1 := pow_lt_one₀ hx0.le hx1 (by omega)
      linarith⟩
  have hPne : P ≠ 0 := by
    have := ModularForm.eta_tprod_ne_zero (z := I * s) (by show 0 < (I * (s : ℂ)).im; simpa using hs)
    simpa only [ModularForm.eta_q_eq_pow, hq] using this
  have hPr : P = (P.re : ℂ) := ext (by simp) (by simp [hmem.1])
  have hPpos : 0 < P.re := lt_of_le_of_ne hmem.2 (fun h => hPne (by rw [hPr, ← h]; simp))
  refine ⟨Real.exp (-(2 * π * s) / 24) * P.re, by positivity, ?_⟩
  rw [ModularForm.eta]
  simp only [ModularForm.eta_q_eq_pow, hq]
  rw [← hPdef, Function.Periodic.qParam]
  push_cast
  rw [← hPr]; congr 1; congr 1; ring_nf; rw [I_sq]; ring

/-- The principal root in 20.7.34 is the eta quotient on the imaginary axis (helper). -/
lemma p20R1_rect_root {t : ℝ} (ht : 0 < t) :
    (jacobiThetaTwoNullTau (2 * (I * t)) * jacobiThetaFourNullTau (2 * (I * t)) / 2) ^ (1 / 2 : ℂ) =
      ModularForm.eta (I * t) * ModularForm.eta (4 * (I * t)) / ModularForm.eta (2 * (I * t)) := by
  have hτ : 0 < (I * (t : ℂ)).im := by simpa using ht
  obtain ⟨r1, hr1, e1⟩ := p20R1_eta_imag ht
  obtain ⟨r2, hr2, e2⟩ := p20R1_eta_imag (show 0 < 2 * t by linarith)
  obtain ⟨r4, hr4, e4⟩ := p20R1_eta_imag (show 0 < 4 * t by linarith)
  have hW : ModularForm.eta (I * t) * ModularForm.eta (4 * (I * t)) / ModularForm.eta (2 * (I * t)) =
      ((r1 * r4 / r2 : ℝ) : ℂ) := by
    rw [show 4 * (I * (t : ℂ)) = I * ((4 * t : ℝ) : ℂ) by push_cast; ring,
      show 2 * (I * (t : ℂ)) = I * ((2 * t : ℝ) : ℂ) by push_cast; ring, e1, e2, e4]
    push_cast; ring
  -- the null value θ₂(0|τ+½) is nonzero
  have hη2 : ModularForm.eta (2 * (I * t)) ≠ 0 :=
    ModularForm.eta_ne_zero (by show 0 < (2 * (I * (t : ℂ))).im; simpa using ht)
  have hN : jacobiThetaTwoTau 0 (I * t + 1 / 2) ≠ 0 := by
    intro h0
    have key := p20R1_two_null_half_eta hτ
    rw [jacobiThetaTwoNullTau, h0, zero_mul] at key
    have : ModularForm.eta (I * t) * ModularForm.eta (4 * (I * t)) ≠ 0 :=
      mul_ne_zero (ModularForm.eta_ne_zero (by show 0 < (I * (t : ℂ)).im; simpa using ht))
        (ModularForm.eta_ne_zero (by show 0 < (4 * (I * (t : ℂ))).im; simpa using ht))
    exact this (by
      have h2 : (2 : ℂ) * cexp (π * I / 8) ≠ 0 := mul_ne_zero two_ne_zero (exp_ne_zero _)
      exact (mul_eq_zero.mp key.symm).resolve_left h2)
  have hsq := (jacobiTheta_reduction_iq_sq 0 (I * t) hτ).2 hN
  have heta := ((p20R1_iq_ratio 0 (I * t) hτ).2 hN).trans (p20R1_ratio_eta hτ)
  rw [heta, hW] at hsq
  have hX : jacobiThetaTwoNullTau (2 * (I * t)) * jacobiThetaFourNullTau (2 * (I * t)) / 2 =
      ((r1 * r4 / r2 : ℝ) : ℂ) ^ 2 := by
    have he : cexp (-(π * I / 8)) ^ 2 = cexp (-(π * I / 4)) := by
      rw [← exp_nat_mul]; congr 1; push_cast; ring
    have hne : cexp (-(π * I / 4)) ≠ 0 := exp_ne_zero _
    apply mul_left_cancel₀ hne
    rw [← hsq, mul_pow, he]
  rw [hX, hW, ← ofReal_pow, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]

/-- DLMF 20.7.34 as printed (`i^{-1/4} = e^{-iπ/8}`, principal square root), in the rectangular case
`τ = it`, `t > 0`, where it holds.
Corrected from the printed DLMF formula: the principal-root form is only valid up to sign for
general `τ`, so it is restricted here to `τ = it`; the full-domain form is
`jacobiTheta_reduction_iq_eta`. -/
@[dlmf 20.7.E34 "printed form, restricted to the rectangular case τ = it"]
theorem jacobiTheta_reduction_iq_rectangular (z : ℂ) {t : ℝ} (ht : 0 < t) :
    (jacobiThetaOneTau z (I * t + 1 / 2) ≠ 0 →
      jacobiThetaOneTau z (2 * (I * t)) * jacobiThetaThreeTau z (2 * (I * t)) /
        jacobiThetaOneTau z (I * t + 1 / 2) =
        cexp (-(π * I / 8)) * (jacobiThetaTwoNullTau (2 * (I * t)) *
          jacobiThetaFourNullTau (2 * (I * t)) / 2) ^ (1 / 2 : ℂ)) ∧
    (jacobiThetaTwoTau z (I * t + 1 / 2) ≠ 0 →
      jacobiThetaTwoTau z (2 * (I * t)) * jacobiThetaFourTau z (2 * (I * t)) /
        jacobiThetaTwoTau z (I * t + 1 / 2) =
        cexp (-(π * I / 8)) * (jacobiThetaTwoNullTau (2 * (I * t)) *
          jacobiThetaFourNullTau (2 * (I * t)) / 2) ^ (1 / 2 : ℂ)) := by
  have hτ : 0 < (I * (t : ℂ)).im := by simpa using ht
  obtain ⟨h1, h2⟩ := p20R1_iq_ratio z (I * t) hτ
  rw [p20R1_rect_root ht]
  exact ⟨fun h => (h1 h).trans (p20R1_ratio_eta hτ), fun h => (h2 h).trans (p20R1_ratio_eta hτ)⟩

/-- DLMF 20.7.34 (`q² ↔ 2τ`, `iq ↔ τ + 1/2`), **corrected full-domain form**: for all `τ` with
`Im τ > 0`, `θ₁(z|2τ)θ₃(z|2τ)/θ₁(z|τ+½) = θ₂(z|2τ)θ₄(z|2τ)/θ₂(z|τ+½) = e^{-iπ/8} η(τ)η(4τ)/η(2τ)`
with Dedekind's `η` (Mathlib's `ModularForm.eta`, `η(τ) = e^{iπτ/12} ∏ (1 - e^{2πinτ})`), at
nonvanishing denominators. Corrected from the printed DLMF formula: the printed
`e^{-iπ/8} (θ₂(0|2τ)θ₄(0|2τ)/2)^{1/2}` with the principal root is wrong by a sign for some `τ`
(e.g. `τ = -2.19 + 1.29i`); the eta quotient is the holomorphic square root
`q^{1/4} ∏ (1 - q^{8n})(1 - q^{4n-2})` of `θ₂(0|2τ)θ₄(0|2τ)/2` (product forms 20.4.2–20.4.4),
which agrees with the principal root for `τ = it`. Checked with mpmath at 200 random `(z, τ)`. -/
@[dlmf 20.7.E34 "corrected full-domain form: explicit eta-quotient square root"]
theorem jacobiTheta_reduction_iq_eta (z τ : ℂ) (hτ : 0 < τ.im) :
    (jacobiThetaOneTau z (τ + 1 / 2) ≠ 0 →
      jacobiThetaOneTau z (2 * τ) * jacobiThetaThreeTau z (2 * τ) /
        jacobiThetaOneTau z (τ + 1 / 2) =
        cexp (-(π * I / 8)) *
          (ModularForm.eta τ * ModularForm.eta (4 * τ) / ModularForm.eta (2 * τ))) ∧
    (jacobiThetaTwoTau z (τ + 1 / 2) ≠ 0 →
      jacobiThetaTwoTau z (2 * τ) * jacobiThetaFourTau z (2 * τ) /
        jacobiThetaTwoTau z (τ + 1 / 2) =
        cexp (-(π * I / 8)) *
          (ModularForm.eta τ * ModularForm.eta (4 * τ) / ModularForm.eta (2 * τ))) := by
  obtain ⟨h1, h2⟩ := p20R1_iq_ratio z τ hτ
  exact ⟨fun h => (h1 h).trans (p20R1_ratio_eta hτ), fun h => (h2 h).trans (p20R1_ratio_eta hτ)⟩

/-! ### §20.8 Watson's expansions -/

/-- DLMF 20.8.1:
`θ₂(0)θ₃(z)θ₄(z)/θ₂(z) = 2 ∑_{n∈ℤ} (-1)ⁿ q^{n²} e^{2inz}/(q^{-n} e^{-iz} + qⁿ e^{iz})`,
where `θ₂(z|τ) ≠ 0`. Corrected from the printed DLMF formula: the hypothesis `θ₂(z|τ) ≠ 0` is
added, since with Lean's `x / 0 = 0` the left side is false at the zeros of `θ₂`. -/
@[dlmf 20.8.E1]
theorem jacobiTheta_watson_expansion {z τ : ℂ} (hτ : 0 < τ.im) (hz : jacobiThetaTwoTau z τ ≠ 0) :
    HasSum (fun n : ℤ => 2 * ((-1 : ℂ) ^ n * cexp (π * I * τ) ^ (n ^ 2) * cexp (2 * I * n * z) /
        (cexp (π * I * τ) ^ (-n) * cexp (-(I * z)) + cexp (π * I * τ) ^ n * cexp (I * z))))
      (jacobiThetaTwoNullTau τ * jacobiThetaThreeTau z τ * jacobiThetaFourTau z τ /
        jacobiThetaTwoTau z τ) := by
  sorry

end DLMF.Theta

end
