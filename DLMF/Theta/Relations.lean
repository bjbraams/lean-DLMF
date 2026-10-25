/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Identities
public import DLMF.Elliptic.ThetaAGM
public import DLMF.JacobiElliptic.Basic
public import DLMF.EllipticIntegrals.Symmetric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Theta functions: relations to other functions (DLMF §20.9)

The modulus `k = θ₂²(0|τ)/θ₃²(0|τ)` (20.9.1), Jacobi's `K = (π/2)θ₃²(0|τ)`, `K' = -iτK`
(20.9.2), the symmetric-integral forms 20.9.3–20.9.5, Jacobi's inversion problem and the
elliptic modular function `k²` (§20.9(ii)).

**Domains.** The project's complete elliptic integral `Real.compEllIntKm` is real, so 20.9.2 is
stated in the rectangular case `τ = it`, `t > 0` (real nome `q = e^{-πt}`), which is DLMF's
principal case (§20.1); for complex `τ` the printed `K(k) = (π/2)θ₃²` holds only on part of the
upper half-plane with the principal branch of `K` (checked numerically): the translates
`F + 2n` of the fundamental region `F` of `Γ(2)`, stated with the complex principal `K` of
Chapter 22 in `compEllIntKk_eq_jacobiThetaThreeNullTau_fundamental`. Carlson's `R_F` is the complex
Chapter 19 integral `DLMF.EllipticIntegrals.symEllIntRF` (DLMF 19.16.1). **Domain correction
(20.9.3):** the printed identity holds for real `z` only when `|z| ≤ π/2` (and `z ≠ 0`, where the
right side is a removable singularity); the left side is `π`-periodic and even in `z` while the
right side is not, and numerically (mpmath, `τ = 0.8i`) the two sides differ for
`z = 1.6, 2, 2.5`. For `τ = it` the identity holds for complex `z` in the open period rectangle
`|Re z| < π/2`, `|Im z| < πt/2`, and for general `τ` it holds near `z = 0`; it fails at some
points of the period parallelogram `π(s + rτ)`, `|s|, |r| < 1/2`, for non-rectangular `τ`.
The relation between
`θⱼ` and the Jacobian and Weierstrass elliptic functions (§20.9(ii), DLMF §§22.2, 23.6(i)) is
acquired in the chapters 22 and 23 modules.

The existing `DLMF.Elliptic.Real.compEllIntKm_eq_jacobiThetaThreeNullQ` proves 20.9.2 for a real
nome in the form `m = 1 - θ₄⁴/θ₃⁴`.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic
open DLMF.EllipticIntegrals (symEllIntRF)

/-- DLMF 20.9.1: the modulus `k = θ₂²(0|τ)/θ₃²(0|τ)`. -/
@[dlmf 20.9.E1]
def thetaModulusK (τ : ℂ) : ℂ := jacobiThetaTwoNullTau τ ^ 2 / jacobiThetaThreeNullTau τ ^ 2

/-- The complementary modulus `k' = θ₄²(0|τ)/θ₃²(0|τ)` (DLMF 20.9.1 with 20.7.5). -/
def thetaComplModulusK (τ : ℂ) : ℂ := jacobiThetaFourNullTau τ ^ 2 / jacobiThetaThreeNullTau τ ^ 2

/-- DLMF 20.9.2 (rectangular case `τ = it`, `t > 0`): with `k = θ₂²(0|it)/θ₃²(0|it)` (real),
`K(k) = (π/2) θ₃²(0|it)` and `K'(k) = K(k') = -iτ K(k) = t K(k)`. Here `K(k) =
Real.compEllIntKm (k²)`.
Corrected from the printed DLMF formula: with the principal complex `K(k)` the printed identity
fails for some complex `τ` (58 of 308 samples), so this form is restricted to `τ = it`; the
full-domain form with its region of validity is
`compEllIntKk_eq_jacobiThetaThreeNullTau_fundamental`. -/
@[dlmf 20.9.E2]
theorem compEllIntK_eq_jacobiThetaThreeNullTau {t : ℝ} (ht : 0 < t) :
    (thetaModulusK (I * t)).im = 0 ∧
    ((Real.compEllIntKm ((thetaModulusK (I * t)).re ^ 2) : ℂ) =
      π / 2 * jacobiThetaThreeNullTau (I * t) ^ 2) ∧
    ((Real.compEllIntKm (1 - (thetaModulusK (I * t)).re ^ 2) : ℂ) =
      -I * (I * t) * Real.compEllIntKm ((thetaModulusK (I * t)).re ^ 2)) := by
  sorry

/-- DLMF 20.9.2, **corrected full-domain form** with the principal complex `K(k)`
(`DLMF.JacobiElliptic.compEllIntKk`, `K'(k) = DLMF.JacobiElliptic.compEllIntKpk`): with
`k = θ₂²(0|τ)/θ₃²(0|τ)`, `K(k) = (π/2) θ₃²(0|τ)` and `K'(k) = -iτ K(k)` for `τ` in the
fundamental region `F = {|Re τ| < 1, |τ - 1/2| > 1/2, |τ + 1/2| > 1/2}` of `Γ(2)`, and
`K(k) = (π/2) θ₃²(0|τ)` for every translate `τ + 2n` of `F` (both sides are 2-periodic; `K'`
is not). Corrected from the printed DLMF formula: the printed identity has no condition on `τ`,
but with the principal `K` it fails off these translates (e.g. 58 of 308 random samples).
Checked with mpmath: no failure at 205 + 471 points of `F` and exact agreement of the region
`⋃ₙ (F + 2n)` with the set where `K = (π/2)θ₃²` holds at 500 random points. -/
@[dlmf 20.9.E2 "corrected full-domain form: region of validity of the principal K"]
theorem compEllIntKk_eq_jacobiThetaThreeNullTau_fundamental {τ : ℂ} (hτ : 0 < τ.im)
    (hre : |τ.re| < 1) (h₁ : 1 / 2 < ‖τ - 1 / 2‖) (h₂ : 1 / 2 < ‖τ + 1 / 2‖) :
    DLMF.JacobiElliptic.compEllIntKk (thetaModulusK τ) =
        π / 2 * jacobiThetaThreeNullTau τ ^ 2 ∧
      DLMF.JacobiElliptic.compEllIntKpk (thetaModulusK τ) =
        -I * τ * DLMF.JacobiElliptic.compEllIntKk (thetaModulusK τ) ∧
      ∀ n : ℤ, DLMF.JacobiElliptic.compEllIntKk (thetaModulusK (τ + 2 * n)) =
        π / 2 * jacobiThetaThreeNullTau (τ + 2 * n) ^ 2 := by
  sorry

/-- DLMF 20.9.3 (rectangular case, **domain-corrected**): for `τ = it`, `t > 0`, and real `z` with
`0 < |z| ≤ π/2`, `R_F(θ₂²(z)/θ₂²(0), θ₃²(z)/θ₃²(0), θ₄²(z)/θ₄²(0)) = z θ₁'(0)/θ₁(z)`.
Corrected from the printed DLMF formula: the printed identity has no branch condition, but the
left side is `π`-periodic and even in real `z` and the right side is not (it fails at
`z = 1.6`, `τ = 0.8i`); the true condition is a branch condition (continuation from `z = 0`).
`R_F` is the complex `symEllIntRF` at the real arguments; the complex-`z` forms are
`carlsonRF_jacobiTheta_rect` and `carlsonRF_jacobiTheta_eventually`. -/
@[dlmf 20.9.E3 "domain-corrected: valid for real 0 < |z| ≤ π/2"]
theorem carlsonRF_jacobiTheta {t : ℝ} (ht : 0 < t) {x : ℝ} (hx0 : 0 < |x|) (hx : |x| ≤ π / 2) :
    symEllIntRF
      ((jacobiThetaTwoTau x (I * t) ^ 2 / jacobiThetaTwoNullTau (I * t) ^ 2).re : ℂ)
      ((jacobiThetaThreeTau x (I * t) ^ 2 / jacobiThetaThreeNullTau (I * t) ^ 2).re : ℂ)
      ((jacobiThetaFourTau x (I * t) ^ 2 / jacobiThetaFourNullTau (I * t) ^ 2).re : ℂ) =
      jacobiThetaOneDerivNullTau (I * t) / jacobiThetaOneTau x (I * t) * x := by
  sorry

/-- DLMF 20.9.3, **corrected complex form** (rectangular case): for `τ = it`, `t > 0`, and
complex `z ≠ 0` in the open period rectangle `|Re z| < π/2`, `|Im z| < πt/2`,
`R_F(θ₂²(z)/θ₂²(0), θ₃²(z)/θ₃²(0), θ₄²(z)/θ₄²(0)) = z θ₁'(0)/θ₁(z)` with the complex `R_F` of
DLMF 19.16.1. Corrected from the printed DLMF formula, which has no condition on `z`: the
printed identity fails at real `z = 1.6` (`τ = 0.8i`) and, for `τ = it`, at 373 of 500 sampled
points with `π t/2 < |Im z| < 0.9 π t`. Checked with mpmath (`elliprf`, `jtheta`): no failure at
3500 points of the rectangle, including points within `10⁻⁴` of its edges, for
`0.05 ≤ t ≤ 4`. -/
@[dlmf 20.9.E3 "corrected complex form: τ = it, z in the open period rectangle"]
theorem carlsonRF_jacobiTheta_rect {t : ℝ} (ht : 0 < t) {z : ℂ} (hz0 : z ≠ 0)
    (hre : |z.re| < π / 2) (him : |z.im| < π * t / 2) :
    symEllIntRF
      (jacobiThetaTwoTau z (I * t) ^ 2 / jacobiThetaTwoNullTau (I * t) ^ 2)
      (jacobiThetaThreeTau z (I * t) ^ 2 / jacobiThetaThreeNullTau (I * t) ^ 2)
      (jacobiThetaFourTau z (I * t) ^ 2 / jacobiThetaFourNullTau (I * t) ^ 2) =
      jacobiThetaOneDerivNullTau (I * t) / jacobiThetaOneTau z (I * t) * z := by
  sorry

/-- DLMF 20.9.3, **corrected complex form** (general `τ`): for every `τ` in the upper half-plane
the identity `R_F(θ₂²(z)/θ₂²(0), θ₃²(z)/θ₃²(0), θ₄²(z)/θ₄²(0)) = z θ₁'(0)/θ₁(z)` holds for all
`z ≠ 0` in a neighbourhood of `0` (the branch of `R_F` continued from `z = 0`, where all three
arguments equal `1`). Corrected from the printed DLMF formula, which has no condition on `z`:
for non-rectangular `τ` the identity fails at some points of the period parallelogram
`π(s + rτ)`, `|s|, |r| < 1/2` (e.g. `τ = 0.448 + 0.520i`, `s = -0.400`, `r = -0.318`; 362 of
3000 samples with `τ` in the `Γ(2)` fundamental region). Checked with mpmath: no failure at
1000 random `τ` with `|z| ≤ 0.07 min(1, Im τ)`. -/
@[dlmf 20.9.E3 "corrected complex form: general τ, z near 0"]
theorem carlsonRF_jacobiTheta_eventually {τ : ℂ} (hτ : 0 < τ.im) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      symEllIntRF
        (jacobiThetaTwoTau z τ ^ 2 / jacobiThetaTwoNullTau τ ^ 2)
        (jacobiThetaThreeTau z τ ^ 2 / jacobiThetaThreeNullTau τ ^ 2)
        (jacobiThetaFourTau z τ ^ 2 / jacobiThetaFourNullTau τ ^ 2) =
        jacobiThetaOneDerivNullTau τ / jacobiThetaOneTau z τ * z := by
  sorry

/-- DLMF 20.9.4 (rectangular case `τ = it`): `R_F(0, θ₃⁴(0,q), θ₄⁴(0,q)) = π/2`. -/
@[dlmf 20.9.E4]
theorem carlsonRF_zero_jacobiThetaNull {t : ℝ} (ht : 0 < t) :
    symEllIntRF 0 ((jacobiThetaThreeNullTau (I * t) ^ 4).re : ℂ)
      ((jacobiThetaFourNullTau (I * t) ^ 4).re : ℂ) = π / 2 := by
  sorry

/-- DLMF 20.9.5 (rectangular case `τ = it`, real nome `q = e^{-πt}`):
`exp(-π R_F(0, k², 1)/R_F(0, k'², 1)) = q` with `k = θ₂²(0)/θ₃²(0)`, `k'² = 1 - k²`. -/
@[dlmf 20.9.E5]
theorem exp_carlsonRF_ratio_eq_nome {t : ℝ} (ht : 0 < t) :
    Complex.exp (-(π * symEllIntRF 0 (((thetaModulusK (I * t)).re ^ 2 : ℝ) : ℂ) 1 /
      symEllIntRF 0 ((1 - (thetaModulusK (I * t)).re ^ 2 : ℝ) : ℂ) 1)) =
      Real.exp (-(π * t)) := by
  sorry

/-- DLMF §20.9(ii): Jacobi's inversion problem. Every modulus `0 < k < 1` is `θ₂²(0|it)/θ₃²(0|it)`
for exactly one `t > 0` (and then `t = K'(k)/K(k)` by 20.9.2). -/
@[dlmf 20.9.ii]
theorem thetaModulusK_inversion {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∃! t : ℝ, 0 < t ∧ thetaModulusK (I * t) = k := by
  sorry

/-- DLMF §20.9(ii): `k² = θ₂⁴(0|τ)/θ₃⁴(0|τ)` is the elliptic modular function `λ(τ)`: it is
invariant
under `τ ↦ τ + 2` and satisfies `λ(-1/τ) = 1 - λ(τ)` (compare DLMF 23.15.2, 23.15.6). -/
@[dlmf 20.9.ii]
theorem thetaModulusK_sq_modular {τ : ℂ} (hτ : 0 < τ.im) :
    thetaModulusK (τ + 2) ^ 2 = thetaModulusK τ ^ 2 ∧
      thetaModulusK (-1 / τ) ^ 2 = 1 - thetaModulusK τ ^ 2 := by
  obtain ⟨h2, h3, h4⟩ := jacobiThetaNullTau_ne_zero hτ
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  constructor
  · have he : cexp (π * I / 4) ^ 8 = 1 := by
      rw [← exp_nat_mul, show ((8 : ℕ) : ℂ) * (π * I / 4) = 2 * π * I by push_cast; ring,
        exp_two_pi_mul_I]
    simp only [thetaModulusK, jacobiThetaTwoNullTau, jacobiThetaThreeNullTau]
    rw [show τ + 2 = τ + 1 + 1 by ring, jacobiThetaTwoTau_add_one, jacobiThetaTwoTau_add_one,
      jacobiThetaThreeTau_add_one, jacobiThetaFourTau_add_one]
    calc ((cexp (π * I / 4) * (cexp (π * I / 4) * jacobiThetaTwoTau 0 τ)) ^ 2 /
          jacobiThetaThreeTau 0 τ ^ 2) ^ 2 =
        cexp (π * I / 4) ^ 8 * (jacobiThetaTwoTau 0 τ ^ 2 / jacobiThetaThreeTau 0 τ ^ 2) ^ 2 := by
          ring
      _ = _ := by rw [he, one_mul]
  · have hc : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 :=
      cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ0))
    have e3 := jacobiThetaThreeTau_neg_inv hτ 0
    have e4 := jacobiThetaFourTau_neg_inv hτ 0
    simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_div, exp_zero, one_mul] at e3 e4
    have h5 := jacobiThetaNull_fourth_power τ hτ
    simp only [thetaModulusK, jacobiThetaTwoNullTau, jacobiThetaThreeNullTau,
      jacobiThetaFourNullTau] at h2 h3 h5 ⊢
    rw [← e3, ← e4]
    field_simp
    linear_combination (-1 : ℂ) * h5

end DLMF.Theta

end
