/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic
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

/-! ### §20.7(i) Sums of squares -/

/-- DLMF 20.7.1: `θ₃²(0) θ₃²(z) = θ₄²(0) θ₄²(z) + θ₂²(0) θ₂²(z)`. -/
@[dlmf 20.7.E1]
theorem jacobiTheta_sq_three_three (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeNullTau τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 =
      jacobiThetaFourNullTau τ ^ 2 * jacobiThetaFourTau z τ ^ 2 +
        jacobiThetaTwoNullTau τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 := by
  sorry

/-- DLMF 20.7.2: `θ₃²(0) θ₄²(z) = θ₂²(0) θ₁²(z) + θ₄²(0) θ₃²(z)`. -/
@[dlmf 20.7.E2]
theorem jacobiTheta_sq_three_four (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeNullTau τ ^ 2 * jacobiThetaFourTau z τ ^ 2 =
      jacobiThetaTwoNullTau τ ^ 2 * jacobiThetaOneTau z τ ^ 2 +
        jacobiThetaFourNullTau τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 := by
  sorry

/-- DLMF 20.7.3: `θ₂²(0) θ₄²(z) = θ₃²(0) θ₁²(z) + θ₄²(0) θ₂²(z)`. -/
@[dlmf 20.7.E3]
theorem jacobiTheta_sq_two_four (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoNullTau τ ^ 2 * jacobiThetaFourTau z τ ^ 2 =
      jacobiThetaThreeNullTau τ ^ 2 * jacobiThetaOneTau z τ ^ 2 +
        jacobiThetaFourNullTau τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 := by
  sorry

/-- DLMF 20.7.4: `θ₂²(0) θ₃²(z) = θ₄²(0) θ₁²(z) + θ₃²(0) θ₂²(z)`. -/
@[dlmf 20.7.E4]
theorem jacobiTheta_sq_two_three (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoNullTau τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 =
      jacobiThetaFourNullTau τ ^ 2 * jacobiThetaOneTau z τ ^ 2 +
        jacobiThetaThreeNullTau τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 := by
  sorry

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
  sorry

/-- DLMF 20.7.7: `θ₄²(0) θ₂(w+z) θ₂(w-z) = θ₄²(w) θ₂²(z) - θ₁²(w) θ₃²(z)`. -/
@[dlmf 20.7.E7]
theorem jacobiThetaTwoTau_add_mul_sub (w z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaFourNullTau τ ^ 2 * jacobiThetaTwoTau (w + z) τ * jacobiThetaTwoTau (w - z) τ =
      jacobiThetaFourTau w τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 -
        jacobiThetaOneTau w τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 := by
  sorry

/-- DLMF 20.7.8: `θ₄²(0) θ₃(w+z) θ₃(w-z) = θ₄²(w) θ₃²(z) - θ₁²(w) θ₂²(z)`. -/
@[dlmf 20.7.E8]
theorem jacobiThetaThreeTau_add_mul_sub (w z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaFourNullTau τ ^ 2 * jacobiThetaThreeTau (w + z) τ * jacobiThetaThreeTau (w - z) τ =
      jacobiThetaFourTau w τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 -
        jacobiThetaOneTau w τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 := by
  sorry

/-- DLMF 20.7.9: `θ₄²(0) θ₄(w+z) θ₄(w-z) = θ₃²(w) θ₃²(z) - θ₂²(w) θ₂²(z)`. -/
@[dlmf 20.7.E9]
theorem jacobiThetaFourTau_add_mul_sub (w z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaFourNullTau τ ^ 2 * jacobiThetaFourTau (w + z) τ * jacobiThetaFourTau (w - z) τ =
      jacobiThetaThreeTau w τ ^ 2 * jacobiThetaThreeTau z τ ^ 2 -
        jacobiThetaTwoTau w τ ^ 2 * jacobiThetaTwoTau z τ ^ 2 := by
  sorry

/-! ### §20.7(iii) Duplication formula -/

/-- DLMF 20.7.10: `θ₁(2z) = 2 θ₁(z) θ₂(z) θ₃(z) θ₄(z) / (θ₂(0) θ₃(0) θ₄(0))`, `Im τ > 0`. -/
@[dlmf 20.7.E10]
theorem jacobiThetaOneTau_two_mul (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaOneTau (2 * z) τ = 2 * (jacobiThetaOneTau z τ * jacobiThetaTwoTau z τ *
      jacobiThetaThreeTau z τ * jacobiThetaFourTau z τ) /
        (jacobiThetaTwoNullTau τ * jacobiThetaThreeNullTau τ * jacobiThetaFourNullTau τ) := by
  sorry

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
  sorry

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
  sorry

/-! ### §20.7(v) Watson's identities -/

/-- DLMF 20.7.13: `θ₁(z|τ)θ₁(w|τ) = θ₃(z+w|2τ)θ₂(z-w|2τ) - θ₂(z+w|2τ)θ₃(z-w|2τ)`. -/
@[dlmf 20.7.E13]
theorem jacobiThetaOneTau_mul_watson (z w τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaOneTau z τ * jacobiThetaOneTau w τ =
      jacobiThetaThreeTau (z + w) (2 * τ) * jacobiThetaTwoTau (z - w) (2 * τ) -
        jacobiThetaTwoTau (z + w) (2 * τ) * jacobiThetaThreeTau (z - w) (2 * τ) := by
  sorry

/-- DLMF 20.7.14: `θ₃(z|τ)θ₃(w|τ) = θ₃(z+w|2τ)θ₃(z-w|2τ) + θ₂(z+w|2τ)θ₂(z-w|2τ)`. -/
@[dlmf 20.7.E14]
theorem jacobiThetaThreeTau_mul_watson (z w τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau z τ * jacobiThetaThreeTau w τ =
      jacobiThetaThreeTau (z + w) (2 * τ) * jacobiThetaThreeTau (z - w) (2 * τ) +
        jacobiThetaTwoTau (z + w) (2 * τ) * jacobiThetaTwoTau (z - w) (2 * τ) := by
  sorry

/-! ### §20.7(vi) Landen transformations -/

/-- DLMF 20.7.15: `A(τ) = 1/θ₄(0|2τ)`. -/
@[dlmf 20.7.E15]
def thetaLandenA (τ : ℂ) : ℂ := 1 / jacobiThetaFourNullTau (2 * τ)

/-- DLMF 20.7.16: `θ₁(2z|2τ) = A θ₁(z|τ) θ₂(z|τ)`. -/
@[dlmf 20.7.E16]
theorem jacobiThetaOneTau_landen (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaOneTau (2 * z) (2 * τ) =
      thetaLandenA τ * jacobiThetaOneTau z τ * jacobiThetaTwoTau z τ := by
  sorry

/-- DLMF 20.7.17: `θ₂(2z|2τ) = A θ₁(π/4 - z|τ) θ₁(π/4 + z|τ)`. -/
@[dlmf 20.7.E17]
theorem jacobiThetaTwoTau_landen (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoTau (2 * z) (2 * τ) =
      thetaLandenA τ * jacobiThetaOneTau (π / 4 - z) τ * jacobiThetaOneTau (π / 4 + z) τ := by
  sorry

/-- DLMF 20.7.18: `θ₃(2z|2τ) = A θ₃(π/4 - z|τ) θ₃(π/4 + z|τ)`. -/
@[dlmf 20.7.E18]
theorem jacobiThetaThreeTau_landen (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau (2 * z) (2 * τ) =
      thetaLandenA τ * jacobiThetaThreeTau (π / 4 - z) τ * jacobiThetaThreeTau (π / 4 + z) τ := by
  sorry

/-- DLMF 20.7.19: `θ₄(2z|2τ) = A θ₃(z|τ) θ₄(z|τ)`. -/
@[dlmf 20.7.E19]
theorem jacobiThetaFourTau_landen (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaFourTau (2 * z) (2 * τ) =
      thetaLandenA τ * jacobiThetaThreeTau z τ * jacobiThetaFourTau z τ := by
  sorry

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
  sorry

/-- DLMF 20.7.22: `θ₂(4z|4τ) = B θ₂(π/8 - z) θ₂(π/8 + z) θ₂(3π/8 - z) θ₂(3π/8 + z)`. -/
@[dlmf 20.7.E22]
theorem jacobiThetaTwoTau_landen_four (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaTwoTau (4 * z) (4 * τ) = thetaLandenB τ * jacobiThetaTwoTau (π / 8 - z) τ *
      jacobiThetaTwoTau (π / 8 + z) τ * jacobiThetaTwoTau (3 * π / 8 - z) τ *
        jacobiThetaTwoTau (3 * π / 8 + z) τ := by
  sorry

/-- DLMF 20.7.23: `θ₃(4z|4τ) = B θ₃(π/8 - z) θ₃(π/8 + z) θ₃(3π/8 - z) θ₃(3π/8 + z)`. -/
@[dlmf 20.7.E23]
theorem jacobiThetaThreeTau_landen_four (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaThreeTau (4 * z) (4 * τ) = thetaLandenB τ * jacobiThetaThreeTau (π / 8 - z) τ *
      jacobiThetaThreeTau (π / 8 + z) τ * jacobiThetaThreeTau (3 * π / 8 - z) τ *
        jacobiThetaThreeTau (3 * π / 8 + z) τ := by
  sorry

/-- DLMF 20.7.24: `θ₄(4z|4τ) = B θ₄(z|τ) θ₄(π/4 - z|τ) θ₄(π/4 + z|τ) θ₃(z|τ)`. -/
@[dlmf 20.7.E24]
theorem jacobiThetaFourTau_landen_four (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaFourTau (4 * z) (4 * τ) = thetaLandenB τ * jacobiThetaFourTau z τ *
      jacobiThetaFourTau (π / 4 - z) τ * jacobiThetaFourTau (π / 4 + z) τ *
        jacobiThetaThreeTau z τ := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
