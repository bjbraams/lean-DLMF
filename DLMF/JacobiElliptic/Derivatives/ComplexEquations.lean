/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Derivatives.ThetaWronskians

/-!
# Complex differential equations of Jacobi functions

First- and second-order differential equations for the complex Jacobian elliptic quotients.

Source references and common attribution are retained in
`DLMF.JacobiElliptic.Derivatives`.
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
theorem deriv_jacobiSnk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiSnk z k) z ^ 2 =
      (1 - jacobiSnk z k ^ 2) * (1 - k ^ 2 * jacobiSnk z k ^ 2) := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 := R.2
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiSnk hk hz).deriv]
  linear_combination ((jacobiDnk z k) ^ 2) * R1 + (1 - (jacobiSnk z k) ^ 2) * R2

/-- DLMF 22.13.2: `(cn')² = (1 - cn²)(k'² + k² cn²)`, away from the poles. -/
@[dlmf 22.13.E2 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiCnk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiCnk z k) z ^ 2 =
      (1 - jacobiCnk z k ^ 2) * (jacobiComodulusk k ^ 2 + k ^ 2 * jacobiCnk z k ^ 2) := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 := R.2
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiCnk hk hz).deriv]
  linear_combination ((jacobiCnk z k) ^ 2 * k ^ 2 - k ^ 2 * (jacobiSnk z k) ^ 2 +
    (jacobiComodulusk k) ^ 2) * R1 + ((jacobiSnk z k) ^ 2) * R2 + (-(jacobiSnk z k) ^ 2) * hK

/-- DLMF 22.13.3: `(dn')² = (1 - dn²)(dn² - k'²)`, away from the poles. -/
@[dlmf 22.13.E3 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiDnk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiDnk z k) z ^ 2 =
      (1 - jacobiDnk z k ^ 2) * (jacobiDnk z k ^ 2 - jacobiComodulusk k ^ 2) := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 := R.2
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiDnk hk hz).deriv]
  linear_combination (k ^ 4 * (jacobiSnk z k) ^ 2) * R1 +
    ((jacobiDnk z k) ^ 2 - k ^ 2 * (jacobiSnk z k) ^ 2 - (jacobiComodulusk k) ^ 2) * R2 +
    (k ^ 2 * (jacobiSnk z k) ^ 2) * hK

/-- DLMF 22.13.4: `(cd')² = (1 - cd²)(1 - k² cd²)`, away from the poles. -/
@[dlmf 22.13.E4 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiCdk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiCdk z k) z ^ 2 =
      (1 - jacobiCdk z k ^ 2) * (1 - k ^ 2 * jacobiCdk z k ^ 2) := by
  have R1 := p22R1_sq_d1 hk hz
  have R2 := p22R1_sq_d2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiCdk hk hz).deriv]
  linear_combination (-(jacobiCdk z k) ^ 2 * k ^ 2 +
    k ^ 2 * (jacobiComodulusk k) ^ 2 * (jacobiSdk z k) ^ 2 + 1) * R1 +
    ((jacobiComodulusk k) ^ 4 * (jacobiSdk z k) ^ 2) * R2 +
    ((jacobiComodulusk k) ^ 2 * (jacobiSdk z k) ^ 2) * hK

/-- DLMF 22.13.5: `(sd')² = (1 - k'² sd²)(1 + k² sd²)`, away from the poles. -/
@[dlmf 22.13.E5 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiSdk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiSdk z k) z ^ 2 =
      (1 - jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 2) * (1 + k ^ 2 * jacobiSdk z k ^ 2) := by
  have R1 := p22R1_sq_d1 hk hz
  have R2 := p22R1_sq_d2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiSdk hk hz).deriv]
  linear_combination ((jacobiNdk z k) ^ 2) * R1 +
    (-(jacobiComodulusk k) ^ 2 * (jacobiSdk z k) ^ 2 + 1) * R2

/-- DLMF 22.13.6: `(nd')² = (nd² - 1)(1 - k'² nd²)`, away from the poles. -/
@[dlmf 22.13.E6 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiNdk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiNdk z k) z ^ 2 =
      (jacobiNdk z k ^ 2 - 1) * (1 - jacobiComodulusk k ^ 2 * jacobiNdk z k ^ 2) := by
  have R1 := p22R1_sq_d1 hk hz
  have R2 := p22R1_sq_d2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiNdk hk hz).deriv]
  linear_combination (k ^ 4 * (jacobiSdk z k) ^ 2) * R1 +
    (k ^ 2 * (jacobiComodulusk k) ^ 2 * (jacobiSdk z k) ^ 2 +
    (jacobiComodulusk k) ^ 2 * (jacobiNdk z k) ^ 2 - 1) * R2 + (k ^ 2 * (jacobiSdk z k) ^ 2) * hK

/-- DLMF 22.13.7: `(dc')² = (dc² - 1)(dc² - k²)`, away from the poles. -/
@[dlmf 22.13.E7 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiDck_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiDck z k) z ^ 2 =
      (jacobiDck z k ^ 2 - 1) * (jacobiDck z k ^ 2 - k ^ 2) := by
  have R1 := p22R1_sq_c1 hk hz
  have R2 := p22R1_sq_c2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiDck hk hz).deriv]
  linear_combination ((jacobiComodulusk k) ^ 4 * (jacobiSck z k) ^ 2) * R1 +
    (-(jacobiDck z k) ^ 2 + k ^ 2 - (jacobiComodulusk k) ^ 2 * (jacobiSck z k) ^ 2) * R2 +
    ((jacobiComodulusk k) ^ 2 * (jacobiSck z k) ^ 2) * hK

/-- DLMF 22.13.8: `(nc')² = (k² + k'² nc²)(nc² - 1)`, away from the poles. -/
@[dlmf 22.13.E8 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiNck_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiNck z k) z ^ 2 =
      (k ^ 2 + jacobiComodulusk k ^ 2 * jacobiNck z k ^ 2) * (jacobiNck z k ^ 2 - 1) := by
  have R1 := p22R1_sq_c1 hk hz
  have R2 := p22R1_sq_c2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiNck hk hz).deriv]
  linear_combination (-k ^ 2 - (jacobiComodulusk k) ^ 2 *
    (jacobiNck z k) ^ 2 - (jacobiComodulusk k) ^ 2 * (jacobiSck z k) ^ 2) * R1 +
    ((jacobiSck z k) ^ 2) * R2 + (-(jacobiSck z k) ^ 2) * hK

/-- DLMF 22.13.9: `(sc')² = (1 + sc²)(1 + k'² sc²)`, away from the poles. -/
@[dlmf 22.13.E9 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiSck_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiSck z k) z ^ 2 =
      (1 + jacobiSck z k ^ 2) * (1 + jacobiComodulusk k ^ 2 * jacobiSck z k ^ 2) := by
  have R1 := p22R1_sq_c1 hk hz
  have R2 := p22R1_sq_c2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiSck hk hz).deriv]
  linear_combination ((jacobiDck z k) ^ 2) * R1 + ((jacobiSck z k) ^ 2 + 1) * R2

/-- DLMF 22.13.10: `(ns')² = (ns² - k²)(ns² - 1)`, away from the poles. -/
@[dlmf 22.13.E10 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiNsk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiNsk z k) z ^ 2 =
      (jacobiNsk z k ^ 2 - k ^ 2) * (jacobiNsk z k ^ 2 - 1) := by
  have R1 := p22R1_sq_s1 hk hz
  have R2 := p22R1_sq_s2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiNsk hk hz).deriv]
  linear_combination (-(jacobiCsk z k) ^ 2 + k ^ 2 - (jacobiNsk z k) ^ 2) * R1 +
    ((jacobiCsk z k) ^ 2) * R2 + ((jacobiCsk z k) ^ 2) * hK

/-- DLMF 22.13.11: `(ds')² = (ds² - k'²)(k² + ds²)`, away from the poles. -/
@[dlmf 22.13.E11 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiDsk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiDsk z k) z ^ 2 =
      (jacobiDsk z k ^ 2 - jacobiComodulusk k ^ 2) * (k ^ 2 + jacobiDsk z k ^ 2) := by
  have R1 := p22R1_sq_s1 hk hz
  have R2 := p22R1_sq_s2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiDsk hk hz).deriv]
  linear_combination ((jacobiCsk z k) ^ 2) * R1 +
    (-(jacobiCsk z k) ^ 2 - (jacobiDsk z k) ^ 2 - k ^ 2) * R2 + (-(jacobiCsk z k) ^ 2) * hK

/-- DLMF 22.13.12: `(cs')² = (1 + cs²)(k'² + cs²)`, away from the poles. -/
@[dlmf 22.13.E12 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiCsk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiCsk z k) z ^ 2 =
      (1 + jacobiCsk z k ^ 2) * (jacobiComodulusk k ^ 2 + jacobiCsk z k ^ 2) := by
  have R1 := p22R1_sq_s1 hk hz
  have R2 := p22R1_sq_s2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiCsk hk hz).deriv]
  linear_combination ((jacobiDsk z k) ^ 2) * R1 + ((jacobiCsk z k) ^ 2 + 1) * R2

/-! ### Second-order differential equations 22.13.13–22.13.24, complex argument -/

/-- DLMF 22.13.13: `sn'' = -(1 + k²) sn + 2k² sn³`, away from the poles. -/
@[dlmf 22.13.E13 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiSnk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiSnk z k) z =
      -(1 + k ^ 2) * jacobiSnk z k + 2 * k ^ 2 * jacobiSnk z k ^ 3 := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 := R.2
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiSnk z k) w) =ᶠ[𝓝 z]
    fun w => jacobiCnk w k * jacobiDnk w k :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiSnk hk hw).deriv
  have hg :=
    ((hasDerivAt_jacobiCnk hk hz).mul (hasDerivAt_jacobiDnk hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-k ^ 2 * (jacobiSnk z k)) * R1 + (-(jacobiSnk z k)) * R2

/-- DLMF 22.13.14: `cn'' = -(k'² - k²) cn - 2k² cn³`, away from the poles. -/
@[dlmf 22.13.E14 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiCnk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiCnk z k) z =
      -(jacobiComodulusk k ^ 2 - k ^ 2) * jacobiCnk z k - 2 * k ^ 2 * jacobiCnk z k ^ 3 := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 := R.2
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiCnk z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiSnk w k * jacobiDnk w k) :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiCnk hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiSnk hk hz).mul (hasDerivAt_jacobiDnk hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (2 * (jacobiCnk z k) * k ^ 2) * R1 + (-(jacobiCnk z k)) * R2 +
    ((jacobiCnk z k)) * hK

/-- DLMF 22.13.15: `dn'' = (1 + k'²) dn - 2 dn³`, away from the poles. -/
@[dlmf 22.13.E15 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiDnk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiDnk z k) z =
      (1 + jacobiComodulusk k ^ 2) * jacobiDnk z k - 2 * jacobiDnk z k ^ 3 := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 := R.2
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiDnk z k) w) =ᶠ[𝓝 z]
    fun w => -(k ^ 2 * jacobiSnk w k * jacobiCnk w k) :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiDnk hk hw).deriv
  have hg :=
    ((((hasDerivAt_jacobiSnk hk hz).const_mul (k ^ 2)).mul
      (hasDerivAt_jacobiCnk hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-(jacobiDnk z k) * k ^ 2) * R1 + (2 * (jacobiDnk z k)) * R2 +
    (-(jacobiDnk z k)) * hK

/-- DLMF 22.13.16: `cd'' = -(1 + k²) cd + 2k² cd³`, away from the poles. -/
@[dlmf 22.13.E16 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiCdk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiCdk z k) z =
      -(1 + k ^ 2) * jacobiCdk z k + 2 * k ^ 2 * jacobiCdk z k ^ 3 := by
  have R1 := p22R1_sq_d1 hk hz
  have R2 := p22R1_sq_d2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiCdk z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiComodulusk k ^ 2 * jacobiSdk w k * jacobiNdk w k) :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiCdk hk hw).deriv
  have hg :=
    ((((hasDerivAt_jacobiSdk hk hz).const_mul (jacobiComodulusk k ^ 2)).mul
      (hasDerivAt_jacobiNdk hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-2 * (jacobiCdk z k) * k ^ 2) * R1 +
    (-(jacobiCdk z k) * (jacobiComodulusk k) ^ 2) * R2 + (-(jacobiCdk z k)) * hK

/-- DLMF 22.13.17: `sd'' = (k² - k'²) sd - 2k²k'² sd³`, away from the poles. -/
@[dlmf 22.13.E17 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiSdk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiSdk z k) z =
      (k ^ 2 - jacobiComodulusk k ^ 2) * jacobiSdk z k -
        2 * k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 3 := by
  have R1 := p22R1_sq_d1 hk hz
  have R2 := p22R1_sq_d2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiSdk z k) w) =ᶠ[𝓝 z]
    fun w => jacobiCdk w k * jacobiNdk w k :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiSdk hk hw).deriv
  have hg :=
    ((hasDerivAt_jacobiCdk hk hz).mul (hasDerivAt_jacobiNdk hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (k ^ 2 * (jacobiSdk z k)) * R1 +
    (-(jacobiComodulusk k) ^ 2 * (jacobiSdk z k)) * R2

/-- DLMF 22.13.18: `nd'' = (1 + k'²) nd - 2k'² nd³`, away from the poles. -/
@[dlmf 22.13.E18 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiNdk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiNdk z k) z =
      (1 + jacobiComodulusk k ^ 2) * jacobiNdk z k -
        2 * jacobiComodulusk k ^ 2 * jacobiNdk z k ^ 3 := by
  have R1 := p22R1_sq_d1 hk hz
  have R2 := p22R1_sq_d2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiNdk z k) w) =ᶠ[𝓝 z]
    fun w => k ^ 2 * jacobiSdk w k * jacobiCdk w k :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiNdk hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiSdk hk hz).const_mul (k ^ 2)).mul
      (hasDerivAt_jacobiCdk hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (k ^ 2 * (jacobiNdk z k)) * R1 +
    (2 * (jacobiComodulusk k) ^ 2 * (jacobiNdk z k)) * R2 + ((jacobiNdk z k)) * hK

/-- DLMF 22.13.19: `dc'' = -(1 + k²) dc + 2 dc³`, away from the poles. -/
@[dlmf 22.13.E19 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiDck (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiDck z k) z =
      -(1 + k ^ 2) * jacobiDck z k + 2 * jacobiDck z k ^ 3 := by
  have R1 := p22R1_sq_c1 hk hz
  have R2 := p22R1_sq_c2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiDck z k) w) =ᶠ[𝓝 z]
    fun w => jacobiComodulusk k ^ 2 * jacobiSck w k * jacobiNck w k :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiDck hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiSck hk hz).const_mul (jacobiComodulusk k ^ 2)).mul
      (hasDerivAt_jacobiNck hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination ((jacobiDck z k) * (jacobiComodulusk k) ^ 2) * R1 +
    (-2 * (jacobiDck z k)) * R2 + ((jacobiDck z k)) * hK

/-- DLMF 22.13.20: `nc'' = (k² - k'²) nc + 2k'² nc³`, away from the poles. -/
@[dlmf 22.13.E20 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiNck (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiNck z k) z =
      (k ^ 2 - jacobiComodulusk k ^ 2) * jacobiNck z k +
        2 * jacobiComodulusk k ^ 2 * jacobiNck z k ^ 3 := by
  have R1 := p22R1_sq_c1 hk hz
  have R2 := p22R1_sq_c2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiNck z k) w) =ᶠ[𝓝 z]
    fun w => jacobiSck w k * jacobiDck w k :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiNck hk hw).deriv
  have hg :=
    ((hasDerivAt_jacobiSck hk hz).mul (hasDerivAt_jacobiDck hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-2 * (jacobiComodulusk k) ^ 2 * (jacobiNck z k)) * R1 +
    ((jacobiNck z k)) * R2 + (-(jacobiNck z k)) * hK

/-- DLMF 22.13.21: `sc'' = (1 + k'²) sc + 2k'² sc³`, away from the poles. -/
@[dlmf 22.13.E21 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiSck (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiSck z k) z =
      (1 + jacobiComodulusk k ^ 2) * jacobiSck z k +
        2 * jacobiComodulusk k ^ 2 * jacobiSck z k ^ 3 := by
  have R1 := p22R1_sq_c1 hk hz
  have R2 := p22R1_sq_c2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiSck z k) w) =ᶠ[𝓝 z]
    fun w => jacobiDck w k * jacobiNck w k :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiSck hk hw).deriv
  have hg :=
    ((hasDerivAt_jacobiDck hk hz).mul (hasDerivAt_jacobiNck hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination ((jacobiComodulusk k) ^ 2 * (jacobiSck z k)) * R1 + ((jacobiSck z k)) * R2

/-- DLMF 22.13.22: `ns'' = -(1 + k²) ns + 2 ns³`, away from the poles. -/
@[dlmf 22.13.E22 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiNsk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiNsk z k) z =
      -(1 + k ^ 2) * jacobiNsk z k + 2 * jacobiNsk z k ^ 3 := by
  have R1 := p22R1_sq_s1 hk hz
  have R2 := p22R1_sq_s2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiNsk z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiDsk w k * jacobiCsk w k) :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiNsk hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiDsk hk hz).mul (hasDerivAt_jacobiCsk hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-2 * (jacobiNsk z k)) * R1 + ((jacobiNsk z k)) * R2 + ((jacobiNsk z k)) * hK

/-- DLMF 22.13.23: `ds'' = (k² - k'²) ds + 2 ds³`, away from the poles. -/
@[dlmf 22.13.E23 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiDsk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiDsk z k) z =
      (k ^ 2 - jacobiComodulusk k ^ 2) * jacobiDsk z k + 2 * jacobiDsk z k ^ 3 := by
  have R1 := p22R1_sq_s1 hk hz
  have R2 := p22R1_sq_s2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiDsk z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiCsk w k * jacobiNsk w k) :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiDsk hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiCsk hk hz).mul (hasDerivAt_jacobiNsk hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination ((jacobiDsk z k)) * R1 + (-2 * (jacobiDsk z k)) * R2 + (-(jacobiDsk z k)) * hK

/-- DLMF 22.13.24: `cs'' = (1 + k'²) cs + 2 cs³`, away from the poles. -/
@[dlmf 22.13.E24 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiCsk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiCsk z k) z =
      (1 + jacobiComodulusk k ^ 2) * jacobiCsk z k + 2 * jacobiCsk z k ^ 3 := by
  have R1 := p22R1_sq_s1 hk hz
  have R2 := p22R1_sq_s2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiCsk z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiNsk w k * jacobiDsk w k) :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiCsk hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiNsk hk hz).mul (hasDerivAt_jacobiDsk hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination ((jacobiCsk z k)) * R1 + ((jacobiCsk z k)) * R2

end Complex

end DLMF.JacobiElliptic
end
end
