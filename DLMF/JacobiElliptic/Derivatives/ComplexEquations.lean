/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Derivatives.ThetaWronskians

/-!
# Complex differential equations of Jacobi functions

The first-order equations DLMF 22.13.1–22.13.12 and the second-order equations
DLMF 22.13.13–22.13.24 for the twelve Jacobian elliptic functions, for complex `z` and
`k ∈ jacobiModulusDomain`, away from the poles.

## Main results

* `deriv_jacobiSn_sq`, `deriv_jacobiCn_sq`, `deriv_jacobiDn_sq`: DLMF 22.13.1–22.13.3, for
  example `(sn')² = (1 - sn²)(1 - k² sn²)`.
* `deriv_jacobiCd_sq`, `deriv_jacobiSd_sq`, `deriv_jacobiNd_sq`, `deriv_jacobiDc_sq`,
  `deriv_jacobiNc_sq`, `deriv_jacobiSc_sq`, `deriv_jacobiNs_sq`, `deriv_jacobiDs_sq`,
  `deriv_jacobiCs_sq`: DLMF 22.13.4–22.13.12.
* `iteratedDeriv_two_jacobiSn`, `iteratedDeriv_two_jacobiCn`, `iteratedDeriv_two_jacobiDn`:
  DLMF 22.13.13–22.13.15, for example `sn'' = -(1 + k²) sn + 2k² sn³`.
* `iteratedDeriv_two_jacobiCd`, …, `iteratedDeriv_two_jacobiCs`: DLMF 22.13.16–22.13.24.

## Implementation notes

The equations are proved from Table 22.13.1 and the sums of squares (DLMF 22.6.1–22.6.4).
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real Topology

noncomputable section

namespace DLMF.JacobiElliptic

local notation "θ₁" => jacobiThetaOneTau

local notation "θ₂" => jacobiThetaTwoTau

local notation "θ₃" => jacobiThetaThreeTau

local notation "θ₄" => jacobiThetaFourTau

section Complex

variable {k : ℂ}

/-! ### First-order differential equations 22.13.1–22.13.12, complex argument -/

/-- DLMF 22.13.1: `(sn')² = (1 - sn²)(1 - k² sn²)`, away from the poles. -/
@[dlmf 22.13.E1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiSn_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    deriv (fun z => jacobiSn z k) z ^ 2 =
      (1 - jacobiSn z k ^ 2) * (1 - k ^ 2 * jacobiSn z k ^ 2) := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSn z k ^ 2 + jacobiDn z k ^ 2 = 1 := R.2
  have hK := jacobiComodulus_sq k
  rw [(hasDerivAt_jacobiSn hk hz).deriv]
  linear_combination ((jacobiDn z k) ^ 2) * R1 + (1 - (jacobiSn z k) ^ 2) * R2

/-- DLMF 22.13.2: `(cn')² = (1 - cn²)(k'² + k² cn²)`, away from the poles. -/
@[dlmf 22.13.E2 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiCn_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    deriv (fun z => jacobiCn z k) z ^ 2 =
      (1 - jacobiCn z k ^ 2) * (jacobiComodulus k ^ 2 + k ^ 2 * jacobiCn z k ^ 2) := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSn z k ^ 2 + jacobiDn z k ^ 2 = 1 := R.2
  have hK := jacobiComodulus_sq k
  rw [(hasDerivAt_jacobiCn hk hz).deriv]
  linear_combination ((jacobiCn z k) ^ 2 * k ^ 2 - k ^ 2 * (jacobiSn z k) ^ 2 +
    (jacobiComodulus k) ^ 2) * R1 + ((jacobiSn z k) ^ 2) * R2 + (-(jacobiSn z k) ^ 2) * hK

/-- DLMF 22.13.3: `(dn')² = (1 - dn²)(dn² - k'²)`, away from the poles. -/
@[dlmf 22.13.E3 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiDn_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    deriv (fun z => jacobiDn z k) z ^ 2 =
      (1 - jacobiDn z k ^ 2) * (jacobiDn z k ^ 2 - jacobiComodulus k ^ 2) := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSn z k ^ 2 + jacobiDn z k ^ 2 = 1 := R.2
  have hK := jacobiComodulus_sq k
  rw [(hasDerivAt_jacobiDn hk hz).deriv]
  linear_combination (k ^ 4 * (jacobiSn z k) ^ 2) * R1 +
    ((jacobiDn z k) ^ 2 - k ^ 2 * (jacobiSn z k) ^ 2 - (jacobiComodulus k) ^ 2) * R2 +
    (k ^ 2 * (jacobiSn z k) ^ 2) * hK

/-- DLMF 22.13.4: `(cd')² = (1 - cd²)(1 - k² cd²)`, away from the poles. -/
@[dlmf 22.13.E4 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiCd_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    deriv (fun z => jacobiCd z k) z ^ 2 =
      (1 - jacobiCd z k ^ 2) * (1 - k ^ 2 * jacobiCd z k ^ 2) := by
  have R1 := jacobiCd_sq_add_jacobiComodulus_sq_mul_jacobiSd_sq hk hz
  have R2 := jacobiNd_sq_sub_sq_mul_jacobiSd_sq hk hz
  have hK := jacobiComodulus_sq k
  rw [(hasDerivAt_jacobiCd hk hz).deriv]
  linear_combination (-(jacobiCd z k) ^ 2 * k ^ 2 +
    k ^ 2 * (jacobiComodulus k) ^ 2 * (jacobiSd z k) ^ 2 + 1) * R1 +
    ((jacobiComodulus k) ^ 4 * (jacobiSd z k) ^ 2) * R2 +
    ((jacobiComodulus k) ^ 2 * (jacobiSd z k) ^ 2) * hK

/-- DLMF 22.13.5: `(sd')² = (1 - k'² sd²)(1 + k² sd²)`, away from the poles. -/
@[dlmf 22.13.E5 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiSd_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    deriv (fun z => jacobiSd z k) z ^ 2 =
      (1 - jacobiComodulus k ^ 2 * jacobiSd z k ^ 2) * (1 + k ^ 2 * jacobiSd z k ^ 2) := by
  have R1 := jacobiCd_sq_add_jacobiComodulus_sq_mul_jacobiSd_sq hk hz
  have R2 := jacobiNd_sq_sub_sq_mul_jacobiSd_sq hk hz
  have hK := jacobiComodulus_sq k
  rw [(hasDerivAt_jacobiSd hk hz).deriv]
  linear_combination ((jacobiNd z k) ^ 2) * R1 +
    (-(jacobiComodulus k) ^ 2 * (jacobiSd z k) ^ 2 + 1) * R2

/-- DLMF 22.13.6: `(nd')² = (nd² - 1)(1 - k'² nd²)`, away from the poles. -/
@[dlmf 22.13.E6 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiNd_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    deriv (fun z => jacobiNd z k) z ^ 2 =
      (jacobiNd z k ^ 2 - 1) * (1 - jacobiComodulus k ^ 2 * jacobiNd z k ^ 2) := by
  have R1 := jacobiCd_sq_add_jacobiComodulus_sq_mul_jacobiSd_sq hk hz
  have R2 := jacobiNd_sq_sub_sq_mul_jacobiSd_sq hk hz
  have hK := jacobiComodulus_sq k
  rw [(hasDerivAt_jacobiNd hk hz).deriv]
  linear_combination (k ^ 4 * (jacobiSd z k) ^ 2) * R1 +
    (k ^ 2 * (jacobiComodulus k) ^ 2 * (jacobiSd z k) ^ 2 +
    (jacobiComodulus k) ^ 2 * (jacobiNd z k) ^ 2 - 1) * R2 + (k ^ 2 * (jacobiSd z k) ^ 2) * hK

/-- DLMF 22.13.7: `(dc')² = (dc² - 1)(dc² - k²)`, away from the poles. -/
@[dlmf 22.13.E7 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiDc_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    deriv (fun z => jacobiDc z k) z ^ 2 =
      (jacobiDc z k ^ 2 - 1) * (jacobiDc z k ^ 2 - k ^ 2) := by
  have R1 := jacobiNc_sq_sub_jacobiSc_sq hk hz
  have R2 := jacobiDc_sq_sub_jacobiComodulus_sq_mul_jacobiSc_sq hk hz
  have hK := jacobiComodulus_sq k
  rw [(hasDerivAt_jacobiDc hk hz).deriv]
  linear_combination ((jacobiComodulus k) ^ 4 * (jacobiSc z k) ^ 2) * R1 +
    (-(jacobiDc z k) ^ 2 + k ^ 2 - (jacobiComodulus k) ^ 2 * (jacobiSc z k) ^ 2) * R2 +
    ((jacobiComodulus k) ^ 2 * (jacobiSc z k) ^ 2) * hK

/-- DLMF 22.13.8: `(nc')² = (k² + k'² nc²)(nc² - 1)`, away from the poles. -/
@[dlmf 22.13.E8 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiNc_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    deriv (fun z => jacobiNc z k) z ^ 2 =
      (k ^ 2 + jacobiComodulus k ^ 2 * jacobiNc z k ^ 2) * (jacobiNc z k ^ 2 - 1) := by
  have R1 := jacobiNc_sq_sub_jacobiSc_sq hk hz
  have R2 := jacobiDc_sq_sub_jacobiComodulus_sq_mul_jacobiSc_sq hk hz
  have hK := jacobiComodulus_sq k
  rw [(hasDerivAt_jacobiNc hk hz).deriv]
  linear_combination (-k ^ 2 - (jacobiComodulus k) ^ 2 *
    (jacobiNc z k) ^ 2 - (jacobiComodulus k) ^ 2 * (jacobiSc z k) ^ 2) * R1 +
    ((jacobiSc z k) ^ 2) * R2 + (-(jacobiSc z k) ^ 2) * hK

/-- DLMF 22.13.9: `(sc')² = (1 + sc²)(1 + k'² sc²)`, away from the poles. -/
@[dlmf 22.13.E9 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiSc_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    deriv (fun z => jacobiSc z k) z ^ 2 =
      (1 + jacobiSc z k ^ 2) * (1 + jacobiComodulus k ^ 2 * jacobiSc z k ^ 2) := by
  have R1 := jacobiNc_sq_sub_jacobiSc_sq hk hz
  have R2 := jacobiDc_sq_sub_jacobiComodulus_sq_mul_jacobiSc_sq hk hz
  have hK := jacobiComodulus_sq k
  rw [(hasDerivAt_jacobiSc hk hz).deriv]
  linear_combination ((jacobiDc z k) ^ 2) * R1 + ((jacobiSc z k) ^ 2 + 1) * R2

/-- DLMF 22.13.10: `(ns')² = (ns² - k²)(ns² - 1)`, away from the poles. -/
@[dlmf 22.13.E10 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiNs_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    deriv (fun z => jacobiNs z k) z ^ 2 =
      (jacobiNs z k ^ 2 - k ^ 2) * (jacobiNs z k ^ 2 - 1) := by
  have R1 := jacobiNs_sq_sub_jacobiCs_sq hk hz
  have R2 := jacobiDs_sq_sub_jacobiCs_sq hk hz
  have hK := jacobiComodulus_sq k
  rw [(hasDerivAt_jacobiNs hk hz).deriv]
  linear_combination (-(jacobiCs z k) ^ 2 + k ^ 2 - (jacobiNs z k) ^ 2) * R1 +
    ((jacobiCs z k) ^ 2) * R2 + ((jacobiCs z k) ^ 2) * hK

/-- DLMF 22.13.11: `(ds')² = (ds² - k'²)(k² + ds²)`, away from the poles. -/
@[dlmf 22.13.E11 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiDs_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    deriv (fun z => jacobiDs z k) z ^ 2 =
      (jacobiDs z k ^ 2 - jacobiComodulus k ^ 2) * (k ^ 2 + jacobiDs z k ^ 2) := by
  have R1 := jacobiNs_sq_sub_jacobiCs_sq hk hz
  have R2 := jacobiDs_sq_sub_jacobiCs_sq hk hz
  have hK := jacobiComodulus_sq k
  rw [(hasDerivAt_jacobiDs hk hz).deriv]
  linear_combination ((jacobiCs z k) ^ 2) * R1 +
    (-(jacobiCs z k) ^ 2 - (jacobiDs z k) ^ 2 - k ^ 2) * R2 + (-(jacobiCs z k) ^ 2) * hK

/-- DLMF 22.13.12: `(cs')² = (1 + cs²)(k'² + cs²)`, away from the poles. -/
@[dlmf 22.13.E12 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiCs_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    deriv (fun z => jacobiCs z k) z ^ 2 =
      (1 + jacobiCs z k ^ 2) * (jacobiComodulus k ^ 2 + jacobiCs z k ^ 2) := by
  have R1 := jacobiNs_sq_sub_jacobiCs_sq hk hz
  have R2 := jacobiDs_sq_sub_jacobiCs_sq hk hz
  have hK := jacobiComodulus_sq k
  rw [(hasDerivAt_jacobiCs hk hz).deriv]
  linear_combination ((jacobiDs z k) ^ 2) * R1 + ((jacobiCs z k) ^ 2 + 1) * R2

/-! ### Second-order differential equations 22.13.13–22.13.24, complex argument -/

/-- DLMF 22.13.13: `sn'' = -(1 + k²) sn + 2k² sn³`, away from the poles. -/
@[dlmf 22.13.E13 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiSn (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiSn z k) z =
      -(1 + k ^ 2) * jacobiSn z k + 2 * k ^ 2 * jacobiSn z k ^ 3 := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSn z k ^ 2 + jacobiDn z k ^ 2 = 1 := R.2
  have hK := jacobiComodulus_sq k
  have hev : (fun w => deriv (fun z => jacobiSn z k) w) =ᶠ[𝓝 z]
    fun w => jacobiCn w k * jacobiDn w k :=
    (eventually_jacobiLetterTheta_ne_zero hk hz).mono fun w hw => (hasDerivAt_jacobiSn hk hw).deriv
  have hg :=
    ((hasDerivAt_jacobiCn hk hz).mul (hasDerivAt_jacobiDn hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-k ^ 2 * (jacobiSn z k)) * R1 + (-(jacobiSn z k)) * R2

/-- DLMF 22.13.14: `cn'' = -(k'² - k²) cn - 2k² cn³`, away from the poles. -/
@[dlmf 22.13.E14 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiCn (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiCn z k) z =
      -(jacobiComodulus k ^ 2 - k ^ 2) * jacobiCn z k - 2 * k ^ 2 * jacobiCn z k ^ 3 := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSn z k ^ 2 + jacobiDn z k ^ 2 = 1 := R.2
  have hK := jacobiComodulus_sq k
  have hev : (fun w => deriv (fun z => jacobiCn z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiSn w k * jacobiDn w k) :=
    (eventually_jacobiLetterTheta_ne_zero hk hz).mono fun w hw => (hasDerivAt_jacobiCn hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiSn hk hz).mul (hasDerivAt_jacobiDn hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (2 * (jacobiCn z k) * k ^ 2) * R1 + (-(jacobiCn z k)) * R2 +
    ((jacobiCn z k)) * hK

/-- DLMF 22.13.15: `dn'' = (1 + k'²) dn - 2 dn³`, away from the poles. -/
@[dlmf 22.13.E15 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiDn (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiDn z k) z =
      (1 + jacobiComodulus k ^ 2) * jacobiDn z k - 2 * jacobiDn z k ^ 3 := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSn z k ^ 2 + jacobiDn z k ^ 2 = 1 := R.2
  have hK := jacobiComodulus_sq k
  have hev : (fun w => deriv (fun z => jacobiDn z k) w) =ᶠ[𝓝 z]
    fun w => -(k ^ 2 * jacobiSn w k * jacobiCn w k) :=
    (eventually_jacobiLetterTheta_ne_zero hk hz).mono fun w hw => (hasDerivAt_jacobiDn hk hw).deriv
  have hg :=
    ((((hasDerivAt_jacobiSn hk hz).const_mul (k ^ 2)).mul
      (hasDerivAt_jacobiCn hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-(jacobiDn z k) * k ^ 2) * R1 + (2 * (jacobiDn z k)) * R2 +
    (-(jacobiDn z k)) * hK

/-- DLMF 22.13.16: `cd'' = -(1 + k²) cd + 2k² cd³`, away from the poles. -/
@[dlmf 22.13.E16 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiCd (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiCd z k) z =
      -(1 + k ^ 2) * jacobiCd z k + 2 * k ^ 2 * jacobiCd z k ^ 3 := by
  have R1 := jacobiCd_sq_add_jacobiComodulus_sq_mul_jacobiSd_sq hk hz
  have R2 := jacobiNd_sq_sub_sq_mul_jacobiSd_sq hk hz
  have hK := jacobiComodulus_sq k
  have hev : (fun w => deriv (fun z => jacobiCd z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiComodulus k ^ 2 * jacobiSd w k * jacobiNd w k) :=
    (eventually_jacobiLetterTheta_ne_zero hk hz).mono fun w hw => (hasDerivAt_jacobiCd hk hw).deriv
  have hg :=
    ((((hasDerivAt_jacobiSd hk hz).const_mul (jacobiComodulus k ^ 2)).mul
      (hasDerivAt_jacobiNd hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-2 * (jacobiCd z k) * k ^ 2) * R1 +
    (-(jacobiCd z k) * (jacobiComodulus k) ^ 2) * R2 + (-(jacobiCd z k)) * hK

/-- DLMF 22.13.17: `sd'' = (k² - k'²) sd - 2k²k'² sd³`, away from the poles. -/
@[dlmf 22.13.E17 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiSd (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiSd z k) z =
      (k ^ 2 - jacobiComodulus k ^ 2) * jacobiSd z k -
        2 * k ^ 2 * jacobiComodulus k ^ 2 * jacobiSd z k ^ 3 := by
  have R1 := jacobiCd_sq_add_jacobiComodulus_sq_mul_jacobiSd_sq hk hz
  have R2 := jacobiNd_sq_sub_sq_mul_jacobiSd_sq hk hz
  have hK := jacobiComodulus_sq k
  have hev : (fun w => deriv (fun z => jacobiSd z k) w) =ᶠ[𝓝 z]
    fun w => jacobiCd w k * jacobiNd w k :=
    (eventually_jacobiLetterTheta_ne_zero hk hz).mono fun w hw => (hasDerivAt_jacobiSd hk hw).deriv
  have hg :=
    ((hasDerivAt_jacobiCd hk hz).mul (hasDerivAt_jacobiNd hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (k ^ 2 * (jacobiSd z k)) * R1 +
    (-(jacobiComodulus k) ^ 2 * (jacobiSd z k)) * R2

/-- DLMF 22.13.18: `nd'' = (1 + k'²) nd - 2k'² nd³`, away from the poles. -/
@[dlmf 22.13.E18 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiNd (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiNd z k) z =
      (1 + jacobiComodulus k ^ 2) * jacobiNd z k -
        2 * jacobiComodulus k ^ 2 * jacobiNd z k ^ 3 := by
  have R1 := jacobiCd_sq_add_jacobiComodulus_sq_mul_jacobiSd_sq hk hz
  have R2 := jacobiNd_sq_sub_sq_mul_jacobiSd_sq hk hz
  have hK := jacobiComodulus_sq k
  have hev : (fun w => deriv (fun z => jacobiNd z k) w) =ᶠ[𝓝 z]
    fun w => k ^ 2 * jacobiSd w k * jacobiCd w k :=
    (eventually_jacobiLetterTheta_ne_zero hk hz).mono fun w hw => (hasDerivAt_jacobiNd hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiSd hk hz).const_mul (k ^ 2)).mul
      (hasDerivAt_jacobiCd hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (k ^ 2 * (jacobiNd z k)) * R1 +
    (2 * (jacobiComodulus k) ^ 2 * (jacobiNd z k)) * R2 + ((jacobiNd z k)) * hK

/-- DLMF 22.13.19: `dc'' = -(1 + k²) dc + 2 dc³`, away from the poles. -/
@[dlmf 22.13.E19 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiDc (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiDc z k) z =
      -(1 + k ^ 2) * jacobiDc z k + 2 * jacobiDc z k ^ 3 := by
  have R1 := jacobiNc_sq_sub_jacobiSc_sq hk hz
  have R2 := jacobiDc_sq_sub_jacobiComodulus_sq_mul_jacobiSc_sq hk hz
  have hK := jacobiComodulus_sq k
  have hev : (fun w => deriv (fun z => jacobiDc z k) w) =ᶠ[𝓝 z]
    fun w => jacobiComodulus k ^ 2 * jacobiSc w k * jacobiNc w k :=
    (eventually_jacobiLetterTheta_ne_zero hk hz).mono fun w hw => (hasDerivAt_jacobiDc hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiSc hk hz).const_mul (jacobiComodulus k ^ 2)).mul
      (hasDerivAt_jacobiNc hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination ((jacobiDc z k) * (jacobiComodulus k) ^ 2) * R1 +
    (-2 * (jacobiDc z k)) * R2 + ((jacobiDc z k)) * hK

/-- DLMF 22.13.20: `nc'' = (k² - k'²) nc + 2k'² nc³`, away from the poles. -/
@[dlmf 22.13.E20 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiNc (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiNc z k) z =
      (k ^ 2 - jacobiComodulus k ^ 2) * jacobiNc z k +
        2 * jacobiComodulus k ^ 2 * jacobiNc z k ^ 3 := by
  have R1 := jacobiNc_sq_sub_jacobiSc_sq hk hz
  have R2 := jacobiDc_sq_sub_jacobiComodulus_sq_mul_jacobiSc_sq hk hz
  have hK := jacobiComodulus_sq k
  have hev : (fun w => deriv (fun z => jacobiNc z k) w) =ᶠ[𝓝 z]
    fun w => jacobiSc w k * jacobiDc w k :=
    (eventually_jacobiLetterTheta_ne_zero hk hz).mono fun w hw => (hasDerivAt_jacobiNc hk hw).deriv
  have hg :=
    ((hasDerivAt_jacobiSc hk hz).mul (hasDerivAt_jacobiDc hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-2 * (jacobiComodulus k) ^ 2 * (jacobiNc z k)) * R1 +
    ((jacobiNc z k)) * R2 + (-(jacobiNc z k)) * hK

/-- DLMF 22.13.21: `sc'' = (1 + k'²) sc + 2k'² sc³`, away from the poles. -/
@[dlmf 22.13.E21 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiSc (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiSc z k) z =
      (1 + jacobiComodulus k ^ 2) * jacobiSc z k +
        2 * jacobiComodulus k ^ 2 * jacobiSc z k ^ 3 := by
  have R1 := jacobiNc_sq_sub_jacobiSc_sq hk hz
  have R2 := jacobiDc_sq_sub_jacobiComodulus_sq_mul_jacobiSc_sq hk hz
  have hK := jacobiComodulus_sq k
  have hev : (fun w => deriv (fun z => jacobiSc z k) w) =ᶠ[𝓝 z]
    fun w => jacobiDc w k * jacobiNc w k :=
    (eventually_jacobiLetterTheta_ne_zero hk hz).mono fun w hw => (hasDerivAt_jacobiSc hk hw).deriv
  have hg :=
    ((hasDerivAt_jacobiDc hk hz).mul (hasDerivAt_jacobiNc hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination ((jacobiComodulus k) ^ 2 * (jacobiSc z k)) * R1 + ((jacobiSc z k)) * R2

/-- DLMF 22.13.22: `ns'' = -(1 + k²) ns + 2 ns³`, away from the poles. -/
@[dlmf 22.13.E22 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiNs (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiNs z k) z =
      -(1 + k ^ 2) * jacobiNs z k + 2 * jacobiNs z k ^ 3 := by
  have R1 := jacobiNs_sq_sub_jacobiCs_sq hk hz
  have R2 := jacobiDs_sq_sub_jacobiCs_sq hk hz
  have hK := jacobiComodulus_sq k
  have hev : (fun w => deriv (fun z => jacobiNs z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiDs w k * jacobiCs w k) :=
    (eventually_jacobiLetterTheta_ne_zero hk hz).mono fun w hw => (hasDerivAt_jacobiNs hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiDs hk hz).mul (hasDerivAt_jacobiCs hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-2 * (jacobiNs z k)) * R1 + ((jacobiNs z k)) * R2 + ((jacobiNs z k)) * hK

/-- DLMF 22.13.23: `ds'' = (k² - k'²) ds + 2 ds³`, away from the poles. -/
@[dlmf 22.13.E23 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiDs (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiDs z k) z =
      (k ^ 2 - jacobiComodulus k ^ 2) * jacobiDs z k + 2 * jacobiDs z k ^ 3 := by
  have R1 := jacobiNs_sq_sub_jacobiCs_sq hk hz
  have R2 := jacobiDs_sq_sub_jacobiCs_sq hk hz
  have hK := jacobiComodulus_sq k
  have hev : (fun w => deriv (fun z => jacobiDs z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiCs w k * jacobiNs w k) :=
    (eventually_jacobiLetterTheta_ne_zero hk hz).mono fun w hw => (hasDerivAt_jacobiDs hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiCs hk hz).mul (hasDerivAt_jacobiNs hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination ((jacobiDs z k)) * R1 + (-2 * (jacobiDs z k)) * R2 + (-(jacobiDs z k)) * hK

/-- DLMF 22.13.24: `cs'' = (1 + k'²) cs + 2 cs³`, away from the poles. -/
@[dlmf 22.13.E24 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiCs (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiThetaArgument z k) (jacobiTau k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiCs z k) z =
      (1 + jacobiComodulus k ^ 2) * jacobiCs z k + 2 * jacobiCs z k ^ 3 := by
  have R1 := jacobiNs_sq_sub_jacobiCs_sq hk hz
  have R2 := jacobiDs_sq_sub_jacobiCs_sq hk hz
  have hK := jacobiComodulus_sq k
  have hev : (fun w => deriv (fun z => jacobiCs z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiNs w k * jacobiDs w k) :=
    (eventually_jacobiLetterTheta_ne_zero hk hz).mono fun w hw => (hasDerivAt_jacobiCs hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiNs hk hz).mul (hasDerivAt_jacobiDs hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination ((jacobiCs z k)) * R1 + ((jacobiCs z k)) * R2

end Complex

end DLMF.JacobiElliptic
end
end
