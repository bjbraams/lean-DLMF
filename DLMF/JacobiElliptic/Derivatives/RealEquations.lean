/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Derivatives.ComplexEquations

/-!
# Real derivatives and differential equations of Jacobi functions

For real argument and real parameter `m = k² < 1`: the entries of Table 22.13.1 for the nine
quotient functions `sd, cd, nd, dc, nc, sc, ns, ds, cs`, and their first- and second-order
differential equations (DLMF 22.13.4–22.13.12 and 22.13.16–22.13.24), proved from the real
`sn, cn, dn`.

## Main results

* `Real.hasDerivAt_jacobiSdm`, `Real.hasDerivAt_jacobiCdm`, `Real.hasDerivAt_jacobiNdm`,
  `Real.hasDerivAt_jacobiDcm`, `Real.hasDerivAt_jacobiNcm`, `Real.hasDerivAt_jacobiScm`,
  `Real.hasDerivAt_jacobiNsm`, `Real.hasDerivAt_jacobiDsm`, `Real.hasDerivAt_jacobiCsm`:
  DLMF Table 22.13.1, real argument.
* `Real.deriv_jacobiCdm_sq`, …, `Real.deriv_jacobiCsm_sq`: DLMF 22.13.4–22.13.12, real
  argument.
* `Real.iteratedDeriv_two_jacobiCdm`, …, `Real.iteratedDeriv_two_jacobiCsm`:
  DLMF 22.13.16–22.13.24, real argument.

## Implementation notes

In the real forms `k'² = 1 - m`, and statements assume `cn u ≠ 0` or `sn u ≠ 0` where DLMF
divides. The entries for `sn, cn, dn` themselves are `Real.hasDerivAt_jacobiSnOfParameter`,
`Real.jacobiSnOfParameter_deriv_sq`, `Real.iteratedDeriv_two_jacobiSnOfParameter` and their
companions in `DLMF.Elliptic.Jacobi` and `DLMF.Elliptic.JacobiIdentities`.
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

/-! ### Real argument: Table 22.13.1 for the nine quotient functions -/

section RealArgument

open Real

variable {m : ℝ}

/-- `sn² + cn² = 1` and `m sn² + dn² = 1` at one point (helper). -/
theorem jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and (hm : m < 1) (u : ℝ) :
    Real.jacobiSnOfParameter u m ^ 2 + Real.jacobiCnOfParameter u m ^ 2 = 1 ∧
      m * Real.jacobiSnOfParameter u m ^ 2 + Real.jacobiDnOfParameter u m ^ 2 = 1 :=
  ⟨Real.jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq u m,
      Real.mul_jacobiSnOfParameter_sq_add_jacobiDnOfParameter_sq hm u⟩

/-- DLMF Table 22.13.1, real argument: `d sd/du = cd nd` with `sd = sn/dn`, `cd = cn/dn`,
`nd = 1/dn`, for real parameter `m < 1`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1"]
theorem Real.hasDerivAt_jacobiSdm (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiSnOfParameter u m / Real.jacobiDnOfParameter u m)
      (Real.jacobiCnOfParameter u m / Real.jacobiDnOfParameter u m *
          (1 / Real.jacobiDnOfParameter u m)) u := by
  have hd := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  refine ((Real.hasDerivAt_jacobiSnOfParameter hm u).div (Real.hasDerivAt_jacobiDnOfParameter hm u)
      hd).congr_deriv ?_
  field_simp
  linear_combination (Real.jacobiCnOfParameter u m) * h2

/-- DLMF Table 22.13.1, real argument: `d cd/du = -k'² sd nd`, `k'² = 1 - m`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1"]
theorem Real.hasDerivAt_jacobiCdm (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiCnOfParameter u m / Real.jacobiDnOfParameter u m)
      (-((1 - m) * (Real.jacobiSnOfParameter u m / Real.jacobiDnOfParameter u m) *
          (1 / Real.jacobiDnOfParameter u m))) u := by
  have hd := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  refine ((Real.hasDerivAt_jacobiCnOfParameter hm u).div (Real.hasDerivAt_jacobiDnOfParameter hm u)
      hd).congr_deriv ?_
  field_simp
  linear_combination -(Real.jacobiSnOfParameter u m) * h2 + m * Real.jacobiSnOfParameter u m * h1

/-- DLMF Table 22.13.1, real argument: `d nd/du = k² sd cd`, `k² = m`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1"]
theorem Real.hasDerivAt_jacobiNdm (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => 1 / Real.jacobiDnOfParameter u m)
      (m * (Real.jacobiSnOfParameter u m / Real.jacobiDnOfParameter u m) *
          (Real.jacobiCnOfParameter u m / Real.jacobiDnOfParameter u m))
      u := by
  have hd := (Real.jacobiDnOfParameter_pos hm u).ne'
  refine ((hasDerivAt_const u (1 : ℝ)).div (Real.hasDerivAt_jacobiDnOfParameter hm u)
      hd).congr_deriv ?_
  field_simp
  ring

/-- DLMF Table 22.13.1, real argument: `d dc/du = k'² sc nc`, where `cn u ≠ 0`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.hasDerivAt_jacobiDcm (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnOfParameter u m ≠ 0) :
    HasDerivAt (fun u => Real.jacobiDnOfParameter u m / Real.jacobiCnOfParameter u m)
      ((1 - m) * (Real.jacobiSnOfParameter u m / Real.jacobiCnOfParameter u m) *
          (1 / Real.jacobiCnOfParameter u m)) u := by
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  refine ((Real.hasDerivAt_jacobiDnOfParameter hm u).div (Real.hasDerivAt_jacobiCnOfParameter hm u)
      hc).congr_deriv ?_
  field_simp
  linear_combination (Real.jacobiSnOfParameter u m) * h2 - m * Real.jacobiSnOfParameter u m * h1

/-- DLMF Table 22.13.1, real argument: `d nc/du = sc dc`, where `cn u ≠ 0`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.hasDerivAt_jacobiNcm (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnOfParameter u m ≠ 0) :
    HasDerivAt (fun u => 1 / Real.jacobiCnOfParameter u m)
      (Real.jacobiSnOfParameter u m / Real.jacobiCnOfParameter u m *
          (Real.jacobiDnOfParameter u m / Real.jacobiCnOfParameter u m)) u := by
  refine ((hasDerivAt_const u (1 : ℝ)).div (Real.hasDerivAt_jacobiCnOfParameter hm u)
      hc).congr_deriv ?_
  field_simp
  ring

/-- DLMF Table 22.13.1, real argument: `d sc/du = dc nc`, where `cn u ≠ 0`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.hasDerivAt_jacobiScm (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnOfParameter u m ≠ 0) :
    HasDerivAt (fun u => Real.jacobiSnOfParameter u m / Real.jacobiCnOfParameter u m)
      (Real.jacobiDnOfParameter u m / Real.jacobiCnOfParameter u m *
          (1 / Real.jacobiCnOfParameter u m)) u := by
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  refine ((Real.hasDerivAt_jacobiSnOfParameter hm u).div (Real.hasDerivAt_jacobiCnOfParameter hm u)
      hc).congr_deriv ?_
  field_simp
  linear_combination (Real.jacobiDnOfParameter u m) * h1

/-- DLMF Table 22.13.1, real argument: `d ns/du = -ds cs`, where `sn u ≠ 0`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.hasDerivAt_jacobiNsm (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnOfParameter u m ≠ 0) :
    HasDerivAt (fun u => 1 / Real.jacobiSnOfParameter u m)
      (-(Real.jacobiDnOfParameter u m / Real.jacobiSnOfParameter u m *
          (Real.jacobiCnOfParameter u m / Real.jacobiSnOfParameter u m)))
      u := by
  refine ((hasDerivAt_const u (1 : ℝ)).div (Real.hasDerivAt_jacobiSnOfParameter hm u)
      hs).congr_deriv ?_
  field_simp
  ring

/-- DLMF Table 22.13.1, real argument: `d ds/du = -cs ns`, where `sn u ≠ 0`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.hasDerivAt_jacobiDsm (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnOfParameter u m ≠ 0) :
    HasDerivAt (fun u => Real.jacobiDnOfParameter u m / Real.jacobiSnOfParameter u m)
      (-(Real.jacobiCnOfParameter u m / Real.jacobiSnOfParameter u m *
          (1 / Real.jacobiSnOfParameter u m))) u := by
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  refine ((Real.hasDerivAt_jacobiDnOfParameter hm u).div (Real.hasDerivAt_jacobiSnOfParameter hm u)
      hs).congr_deriv ?_
  field_simp
  linear_combination -(Real.jacobiCnOfParameter u m) * h2

/-- DLMF Table 22.13.1, real argument: `d cs/du = -ns ds`, where `sn u ≠ 0`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.hasDerivAt_jacobiCsm (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnOfParameter u m ≠ 0) :
    HasDerivAt (fun u => Real.jacobiCnOfParameter u m / Real.jacobiSnOfParameter u m)
      (-(1 / Real.jacobiSnOfParameter u m *
          (Real.jacobiDnOfParameter u m / Real.jacobiSnOfParameter u m))) u := by
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  refine ((Real.hasDerivAt_jacobiCnOfParameter hm u).div (Real.hasDerivAt_jacobiSnOfParameter hm u)
      hs).congr_deriv ?_
  field_simp
  linear_combination -(Real.jacobiDnOfParameter u m) * h1

/-! ### Real argument: first-order equations 22.13.4–22.13.12 -/

/-- DLMF 22.13.4, real argument: the first-order equation of
`cd = Real.jacobiCnOfParameter / Real.jacobiDnOfParameter` for real parameter `m = k² < 1`
(`k'² = 1 - m`). -/
@[dlmf 22.13.E4 "special case: real argument, real parameter m = k² < 1"]
theorem Real.deriv_jacobiCdm_sq (hm : m < 1) (u : ℝ) :
    deriv (fun u => Real.jacobiCnOfParameter u m / Real.jacobiDnOfParameter u m) u ^ 2 =
      (1 - (Real.jacobiCnOfParameter u m / Real.jacobiDnOfParameter u m) ^ 2) *
          (1 - m * (Real.jacobiCnOfParameter u m /
          Real.jacobiDnOfParameter u m) ^ 2) := by
  have hd := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  rw [(Real.hasDerivAt_jacobiCdm hm u).deriv]
  field_simp
  linear_combination (-(Real.jacobiCnOfParameter u m)^2*m +
      (Real.jacobiDnOfParameter u m)^2*m - m + 1) * h1 +
      ((Real.jacobiCnOfParameter u m)^2 - (Real.jacobiDnOfParameter u m)^2 + m - 1) * h2

/-- DLMF 22.13.5, real argument: the first-order equation of
`sd = Real.jacobiSnOfParameter / Real.jacobiDnOfParameter` for real parameter `m = k² < 1`
(`k'² = 1 - m`). -/
@[dlmf 22.13.E5 "special case: real argument, real parameter m = k² < 1"]
theorem Real.deriv_jacobiSdm_sq (hm : m < 1) (u : ℝ) :
    deriv (fun u => Real.jacobiSnOfParameter u m / Real.jacobiDnOfParameter u m) u ^ 2 =
      (1 - (1 - m) * (Real.jacobiSnOfParameter u m / Real.jacobiDnOfParameter u m) ^ 2) * (1 + m *
          (Real.jacobiSnOfParameter u m / Real.jacobiDnOfParameter u m) ^ 2) := by
  have hd := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  rw [(Real.hasDerivAt_jacobiSdm hm u).deriv]
  field_simp
  linear_combination (-(Real.jacobiDnOfParameter u m)^2*m + (Real.jacobiDnOfParameter u m)^2 -
      m^2*(Real.jacobiSnOfParameter u m)^2 + m*(Real.jacobiSnOfParameter u m)^2 + m) * h1 +
          ((Real.jacobiCnOfParameter u m)^2*m -
      (Real.jacobiCnOfParameter u m)^2 - (Real.jacobiDnOfParameter u m)^2 - m) * h2

/-- DLMF 22.13.6, real argument: the first-order equation of `nd = 1 / Real.jacobiDnOfParameter`
for real parameter `m = k² < 1` (`k'² = 1 - m`). -/
@[dlmf 22.13.E6 "special case: real argument, real parameter m = k² < 1"]
theorem Real.deriv_jacobiNdm_sq (hm : m < 1) (u : ℝ) :
    deriv (fun u => 1 / Real.jacobiDnOfParameter u m) u ^ 2 =
      ((1 / Real.jacobiDnOfParameter u m) ^ 2 - 1) *
          (1 - (1 - m) * (1 / Real.jacobiDnOfParameter u m) ^ 2) := by
  have hd := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  rw [(Real.hasDerivAt_jacobiNdm hm u).deriv]
  field_simp
  linear_combination (-(Real.jacobiDnOfParameter u m)^2*m + m) * h1 +
      ((Real.jacobiCnOfParameter u m)^2*m +
      (Real.jacobiDnOfParameter u m)^2 - 1) * h2

/-- DLMF 22.13.7, real argument: the first-order equation of
`dc = Real.jacobiDnOfParameter / Real.jacobiCnOfParameter` for real parameter `m = k² < 1`
(`k'² = 1 - m`), cn u ≠ 0. -/
@[dlmf 22.13.E7 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.deriv_jacobiDcm_sq (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnOfParameter u m ≠ 0) :
    deriv (fun u => Real.jacobiDnOfParameter u m / Real.jacobiCnOfParameter u m) u ^ 2 =
      ((Real.jacobiDnOfParameter u m / Real.jacobiCnOfParameter u m) ^ 2 - 1) *
          ((Real.jacobiDnOfParameter u m /
          Real.jacobiCnOfParameter u m) ^ 2 - m) := by
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  rw [(Real.hasDerivAt_jacobiDcm hm hc).deriv]
  field_simp
  linear_combination (-(Real.jacobiCnOfParameter u m)^2*m +
      (Real.jacobiDnOfParameter u m)^2*m - m + 1) * h1 +
      ((Real.jacobiCnOfParameter u m)^2 - (Real.jacobiDnOfParameter u m)^2 + m - 1) * h2

/-- DLMF 22.13.8, real argument: the first-order equation of `nc = 1 / Real.jacobiCnOfParameter`
for real parameter `m = k² < 1` (`k'² = 1 - m`), cn u ≠ 0. -/
@[dlmf 22.13.E8 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.deriv_jacobiNcm_sq (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnOfParameter u m ≠ 0) :
    deriv (fun u => 1 / Real.jacobiCnOfParameter u m) u ^ 2 =
      (m + (1 - m) * (1 / Real.jacobiCnOfParameter u m) ^ 2) *
          ((1 / Real.jacobiCnOfParameter u m) ^ 2 - 1) := by
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  rw [(Real.hasDerivAt_jacobiNcm hm hc).deriv]
  field_simp
  linear_combination ((Real.jacobiCnOfParameter u m)^2*m +
      (Real.jacobiDnOfParameter u m)^2 - m) * h1 + (1 -
      (Real.jacobiCnOfParameter u m)^2) * h2

/-- DLMF 22.13.9, real argument: the first-order equation of
`sc = Real.jacobiSnOfParameter / Real.jacobiCnOfParameter` for real parameter `m = k² < 1`
(`k'² = 1 - m`), cn u ≠ 0. -/
@[dlmf 22.13.E9 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.deriv_jacobiScm_sq (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnOfParameter u m ≠ 0) :
    deriv (fun u => Real.jacobiSnOfParameter u m / Real.jacobiCnOfParameter u m) u ^ 2 =
      (1 + (Real.jacobiSnOfParameter u m / Real.jacobiCnOfParameter u m) ^ 2) *
          (1 + (1 - m) * (Real.jacobiSnOfParameter u m /
          Real.jacobiCnOfParameter u m) ^ 2) := by
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  rw [(Real.hasDerivAt_jacobiScm hm hc).deriv]
  field_simp
  linear_combination (-(Real.jacobiCnOfParameter u m)^2 + m*(Real.jacobiSnOfParameter u m)^2 -
      (Real.jacobiSnOfParameter u m)^2 -
      1) * h1 + (1) * h2

/-- DLMF 22.13.10, real argument: the first-order equation of `ns = 1 / Real.jacobiSnOfParameter`
for real parameter `m = k² < 1` (`k'² = 1 - m`), sn u ≠ 0. -/
@[dlmf 22.13.E10 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.deriv_jacobiNsm_sq (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnOfParameter u m ≠ 0) :
    deriv (fun u => 1 / Real.jacobiSnOfParameter u m) u ^ 2 =
      ((1 / Real.jacobiSnOfParameter u m) ^ 2 - m) *
          ((1 / Real.jacobiSnOfParameter u m) ^ 2 - 1) := by
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  rw [(Real.hasDerivAt_jacobiNsm hm hs).deriv]
  field_simp
  linear_combination (-m*(Real.jacobiSnOfParameter u m)^2 + 1) * h1 +
      ((Real.jacobiCnOfParameter u m)^2) * h2

/-- DLMF 22.13.11, real argument: the first-order equation of
`ds = Real.jacobiDnOfParameter / Real.jacobiSnOfParameter` for real parameter `m = k² < 1`
(`k'² = 1 - m`), sn u ≠ 0. -/
@[dlmf 22.13.E11 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.deriv_jacobiDsm_sq (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnOfParameter u m ≠ 0) :
    deriv (fun u => Real.jacobiDnOfParameter u m / Real.jacobiSnOfParameter u m) u ^ 2 =
      ((Real.jacobiDnOfParameter u m / Real.jacobiSnOfParameter u m) ^ 2 - (1 - m)) *
          (m + (Real.jacobiDnOfParameter u m /
          Real.jacobiSnOfParameter u m) ^ 2) := by
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  rw [(Real.hasDerivAt_jacobiDsm hm hs).deriv]
  field_simp
  linear_combination (-(Real.jacobiDnOfParameter u m)^2*m + (Real.jacobiDnOfParameter u m)^2 -
      m^2*(Real.jacobiSnOfParameter u m)^2 + m*(Real.jacobiSnOfParameter u m)^2 + m) * h1 +
          ((Real.jacobiCnOfParameter u m)^2*m -
      (Real.jacobiCnOfParameter u m)^2 - (Real.jacobiDnOfParameter u m)^2 - m) * h2

/-- DLMF 22.13.12, real argument: the first-order equation of
`cs = Real.jacobiCnOfParameter / Real.jacobiSnOfParameter` for real parameter `m = k² < 1`
(`k'² = 1 - m`), sn u ≠ 0. -/
@[dlmf 22.13.E12 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.deriv_jacobiCsm_sq (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnOfParameter u m ≠ 0) :
    deriv (fun u => Real.jacobiCnOfParameter u m / Real.jacobiSnOfParameter u m) u ^ 2 =
      (1 + (Real.jacobiCnOfParameter u m / Real.jacobiSnOfParameter u m) ^ 2) *
          ((1 - m) + (Real.jacobiCnOfParameter u m /
          Real.jacobiSnOfParameter u m) ^ 2) := by
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  rw [(Real.hasDerivAt_jacobiCsm hm hs).deriv]
  field_simp
  linear_combination (-(Real.jacobiCnOfParameter u m)^2 + m*(Real.jacobiSnOfParameter u m)^2 -
      (Real.jacobiSnOfParameter u m)^2 -
      1) * h1 + (1) * h2

/-! ### Real argument: second-order equations 22.13.16–22.13.24 -/

/-- DLMF 22.13.16, real argument: the second-order equation of `cd = Real.jacobiCnOfParameter /
Real.jacobiDnOfParameter`
for real parameter `m = k² < 1` (`k'² = 1 - m`). -/
@[dlmf 22.13.E16 "special case: real argument, real parameter m = k² < 1"]
theorem Real.iteratedDeriv_two_jacobiCdm (hm : m < 1) (u : ℝ) :
    iteratedDeriv 2 (fun u => Real.jacobiCnOfParameter u m / Real.jacobiDnOfParameter u m) u =
      -(1 + m) * (Real.jacobiCnOfParameter u m / Real.jacobiDnOfParameter u m) + 2 * m *
          (Real.jacobiCnOfParameter u m /
          Real.jacobiDnOfParameter u m) ^ 3 := by
  have hd0 := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  have h' : HasDerivAt
      (fun v => -((1 - m) * (Real.jacobiSnOfParameter v m / Real.jacobiDnOfParameter v m) * (1 /
      Real.jacobiDnOfParameter v m))) _ u :=
    (((Real.hasDerivAt_jacobiSdm hm u).const_mul (1 - m)).mul (Real.hasDerivAt_jacobiNdm hm u)).neg
  have hd : deriv (fun u => Real.jacobiCnOfParameter u m / Real.jacobiDnOfParameter u m)
      = fun v => _ :=
    funext fun v => (Real.hasDerivAt_jacobiCdm hm v).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd, h'.deriv]
  field_simp
  linear_combination (-2*(Real.jacobiCnOfParameter u m)*m) * h1 +
      ((Real.jacobiCnOfParameter u m)*m +
      (Real.jacobiCnOfParameter u m)) * h2

/-- DLMF 22.13.17, real argument: the second-order equation of `sd = Real.jacobiSnOfParameter /
Real.jacobiDnOfParameter`
for real parameter `m = k² < 1` (`k'² = 1 - m`). -/
@[dlmf 22.13.E17 "special case: real argument, real parameter m = k² < 1"]
theorem Real.iteratedDeriv_two_jacobiSdm (hm : m < 1) (u : ℝ) :
    iteratedDeriv 2 (fun u => Real.jacobiSnOfParameter u m / Real.jacobiDnOfParameter u m) u =
      (m - (1 - m)) * (Real.jacobiSnOfParameter u m / Real.jacobiDnOfParameter u m) -
          2 * m * (1 - m) *
          (Real.jacobiSnOfParameter u m / Real.jacobiDnOfParameter u m) ^ 3 := by
  have hd0 := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  have h' : HasDerivAt
      (fun v => (Real.jacobiCnOfParameter v m / Real.jacobiDnOfParameter v m) * (1 /
      Real.jacobiDnOfParameter v m)) _ u :=
    (Real.hasDerivAt_jacobiCdm hm u).mul (Real.hasDerivAt_jacobiNdm hm u)
  have hd : deriv (fun u => Real.jacobiSnOfParameter u m / Real.jacobiDnOfParameter u m)
      = fun v => _ :=
    funext fun v => (Real.hasDerivAt_jacobiSdm hm v).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd, h'.deriv]
  field_simp
  linear_combination (m*(Real.jacobiSnOfParameter u m)) * h1 +
      (-2*m*(Real.jacobiSnOfParameter u m) +
      (Real.jacobiSnOfParameter u m)) * h2

/-- DLMF 22.13.18, real argument: the second-order equation of `nd = 1 / Real.jacobiDnOfParameter`
for real parameter `m = k² < 1` (`k'² = 1 - m`). -/
@[dlmf 22.13.E18 "special case: real argument, real parameter m = k² < 1"]
theorem Real.iteratedDeriv_two_jacobiNdm (hm : m < 1) (u : ℝ) :
    iteratedDeriv 2 (fun u => 1 / Real.jacobiDnOfParameter u m) u =
      (1 + (1 - m)) * (1 / Real.jacobiDnOfParameter u m) - 2 * (1 - m) *
          (1 / Real.jacobiDnOfParameter u m) ^ 3 := by
  have hd0 := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  have h' : HasDerivAt (fun v => m * (Real.jacobiSnOfParameter v m / Real.jacobiDnOfParameter v m) *
      (Real.jacobiCnOfParameter v m / Real.jacobiDnOfParameter v m)) _ u :=
    ((Real.hasDerivAt_jacobiSdm hm u).const_mul m).mul (Real.hasDerivAt_jacobiCdm hm u)
  have hd : deriv (fun u => 1 / Real.jacobiDnOfParameter u m) = fun v => _ :=
    funext fun v => (Real.hasDerivAt_jacobiNdm hm v).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd, h'.deriv]
  field_simp
  linear_combination (m) * h1 + (m - 2) * h2

/-- DLMF 22.13.19, real argument: the second-order equation of `dc = Real.jacobiDnOfParameter /
Real.jacobiCnOfParameter`
for real parameter `m = k² < 1` (`k'² = 1 - m`), cn u ≠ 0. -/
@[dlmf 22.13.E19 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.iteratedDeriv_two_jacobiDcm (hm : m < 1) {u : ℝ}
    (hc : Real.jacobiCnOfParameter u m ≠ 0) :
    iteratedDeriv 2 (fun u => Real.jacobiDnOfParameter u m / Real.jacobiCnOfParameter u m) u =
      -(1 + m) * (Real.jacobiDnOfParameter u m / Real.jacobiCnOfParameter u m) + 2 *
          (Real.jacobiDnOfParameter u m /
          Real.jacobiCnOfParameter u m) ^ 3 := by
  have hd0 := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  have h' : HasDerivAt
      (fun v => (1 - m) * (Real.jacobiSnOfParameter v m / Real.jacobiCnOfParameter v m) * (1 /
      Real.jacobiCnOfParameter v m)) _ u :=
    ((Real.hasDerivAt_jacobiScm hm hc).const_mul (1 - m)).mul (Real.hasDerivAt_jacobiNcm hm hc)
  have hev : ∀ᶠ v in 𝓝 u, Real.jacobiCnOfParameter v m ≠ 0 :=
    (Real.hasDerivAt_jacobiCnOfParameter hm u).continuousAt.eventually_ne hc
  have hd : deriv (fun u => Real.jacobiDnOfParameter u m / Real.jacobiCnOfParameter u m)
      =ᶠ[𝓝 u] fun v => _ :=
    hev.mono fun v hv => (Real.hasDerivAt_jacobiDcm hm hv).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, h'.deriv]
  field_simp
  linear_combination (m + 1) * h1 + (-2) * h2

/-- DLMF 22.13.20, real argument: the second-order equation of `nc = 1 / Real.jacobiCnOfParameter`
for real parameter `m = k² < 1` (`k'² = 1 - m`), cn u ≠ 0. -/
@[dlmf 22.13.E20 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.iteratedDeriv_two_jacobiNcm (hm : m < 1) {u : ℝ}
    (hc : Real.jacobiCnOfParameter u m ≠ 0) :
    iteratedDeriv 2 (fun u => 1 / Real.jacobiCnOfParameter u m) u =
      (m - (1 - m)) * (1 / Real.jacobiCnOfParameter u m) + 2 * (1 - m) *
          (1 / Real.jacobiCnOfParameter u m) ^ 3 := by
  have hd0 := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  have h' : HasDerivAt
      (fun v => (Real.jacobiSnOfParameter v m / Real.jacobiCnOfParameter v m) *
      (Real.jacobiDnOfParameter v m /
      Real.jacobiCnOfParameter v m)) _ u :=
    (Real.hasDerivAt_jacobiScm hm hc).mul (Real.hasDerivAt_jacobiDcm hm hc)
  have hev : ∀ᶠ v in 𝓝 u, Real.jacobiCnOfParameter v m ≠ 0 :=
    (Real.hasDerivAt_jacobiCnOfParameter hm u).continuousAt.eventually_ne hc
  have hd : deriv (fun u => 1 / Real.jacobiCnOfParameter u m) =ᶠ[𝓝 u] fun v => _ :=
    hev.mono fun v hv => (Real.hasDerivAt_jacobiNcm hm hv).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, h'.deriv]
  field_simp
  linear_combination (1 - 2*m) * h1 + (1) * h2

/-- DLMF 22.13.21, real argument: the second-order equation of `sc = Real.jacobiSnOfParameter /
Real.jacobiCnOfParameter`
for real parameter `m = k² < 1` (`k'² = 1 - m`), cn u ≠ 0. -/
@[dlmf 22.13.E21 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.iteratedDeriv_two_jacobiScm (hm : m < 1) {u : ℝ}
    (hc : Real.jacobiCnOfParameter u m ≠ 0) :
    iteratedDeriv 2 (fun u => Real.jacobiSnOfParameter u m / Real.jacobiCnOfParameter u m) u =
      (1 + (1 - m)) * (Real.jacobiSnOfParameter u m / Real.jacobiCnOfParameter u m) + 2 * (1 - m) *
          (Real.jacobiSnOfParameter u m / Real.jacobiCnOfParameter u m) ^ 3 := by
  have hd0 := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  have h' : HasDerivAt
      (fun v => (Real.jacobiDnOfParameter v m / Real.jacobiCnOfParameter v m) * (1 /
      Real.jacobiCnOfParameter v m)) _ u :=
    (Real.hasDerivAt_jacobiDcm hm hc).mul (Real.hasDerivAt_jacobiNcm hm hc)
  have hev : ∀ᶠ v in 𝓝 u, Real.jacobiCnOfParameter v m ≠ 0 :=
    (Real.hasDerivAt_jacobiCnOfParameter hm u).continuousAt.eventually_ne hc
  have hd : deriv (fun u => Real.jacobiSnOfParameter u m / Real.jacobiCnOfParameter u m)
      =ᶠ[𝓝 u] fun v => _ :=
    hev.mono fun v hv => (Real.hasDerivAt_jacobiScm hm hv).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, h'.deriv]
  field_simp
  linear_combination (m*(Real.jacobiSnOfParameter u m) - 2*(Real.jacobiSnOfParameter u m)) * h1 +
      ((Real.jacobiSnOfParameter u m)) * h2

/-- DLMF 22.13.22, real argument: the second-order equation of `ns = 1 / Real.jacobiSnOfParameter`
for real parameter `m = k² < 1` (`k'² = 1 - m`), sn u ≠ 0. -/
@[dlmf 22.13.E22 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.iteratedDeriv_two_jacobiNsm (hm : m < 1) {u : ℝ}
    (hs : Real.jacobiSnOfParameter u m ≠ 0) :
    iteratedDeriv 2 (fun u => 1 / Real.jacobiSnOfParameter u m) u =
      -(1 + m) * (1 / Real.jacobiSnOfParameter u m) + 2 *
          (1 / Real.jacobiSnOfParameter u m) ^ 3 := by
  have hd0 := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  have h' : HasDerivAt (fun v => -((Real.jacobiDnOfParameter v m / Real.jacobiSnOfParameter v m) *
      (Real.jacobiCnOfParameter v m / Real.jacobiSnOfParameter v m))) _ u :=
    ((Real.hasDerivAt_jacobiDsm hm hs).mul (Real.hasDerivAt_jacobiCsm hm hs)).neg
  have hev : ∀ᶠ v in 𝓝 u, Real.jacobiSnOfParameter v m ≠ 0 :=
    (Real.hasDerivAt_jacobiSnOfParameter hm u).continuousAt.eventually_ne hs
  have hd : deriv (fun u => 1 / Real.jacobiSnOfParameter u m) =ᶠ[𝓝 u] fun v => _ :=
    hev.mono fun v hv => (Real.hasDerivAt_jacobiNsm hm hv).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, h'.deriv]
  field_simp
  linear_combination (1) * h1 + (1) * h2

/-- DLMF 22.13.23, real argument: the second-order equation of `ds = Real.jacobiDnOfParameter /
Real.jacobiSnOfParameter`
for real parameter `m = k² < 1` (`k'² = 1 - m`), sn u ≠ 0. -/
@[dlmf 22.13.E23 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.iteratedDeriv_two_jacobiDsm (hm : m < 1) {u : ℝ}
    (hs : Real.jacobiSnOfParameter u m ≠ 0) :
    iteratedDeriv 2 (fun u => Real.jacobiDnOfParameter u m / Real.jacobiSnOfParameter u m) u =
      (m - (1 - m)) * (Real.jacobiDnOfParameter u m / Real.jacobiSnOfParameter u m) + 2 *
          (Real.jacobiDnOfParameter u m /
          Real.jacobiSnOfParameter u m) ^ 3 := by
  have hd0 := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  have h' : HasDerivAt
      (fun v => -((Real.jacobiCnOfParameter v m / Real.jacobiSnOfParameter v m) * (1 /
      Real.jacobiSnOfParameter v m))) _ u :=
    ((Real.hasDerivAt_jacobiCsm hm hs).mul (Real.hasDerivAt_jacobiNsm hm hs)).neg
  have hev : ∀ᶠ v in 𝓝 u, Real.jacobiSnOfParameter v m ≠ 0 :=
    (Real.hasDerivAt_jacobiSnOfParameter hm u).continuousAt.eventually_ne hs
  have hd : deriv (fun u => Real.jacobiDnOfParameter u m / Real.jacobiSnOfParameter u m)
      =ᶠ[𝓝 u] fun v => _ :=
    hev.mono fun v hv => (Real.hasDerivAt_jacobiDsm hm hv).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, h'.deriv]
  field_simp
  linear_combination (1) * h1 + (-2) * h2

/-- DLMF 22.13.24, real argument: the second-order equation of `cs = Real.jacobiCnOfParameter /
Real.jacobiSnOfParameter`
for real parameter `m = k² < 1` (`k'² = 1 - m`), sn u ≠ 0. -/
@[dlmf 22.13.E24 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.iteratedDeriv_two_jacobiCsm (hm : m < 1) {u : ℝ}
    (hs : Real.jacobiSnOfParameter u m ≠ 0) :
    iteratedDeriv 2 (fun u => Real.jacobiCnOfParameter u m / Real.jacobiSnOfParameter u m) u =
      (1 + (1 - m)) * (Real.jacobiCnOfParameter u m / Real.jacobiSnOfParameter u m) + 2 *
          (Real.jacobiCnOfParameter u m /
          Real.jacobiSnOfParameter u m) ^ 3 := by
  have hd0 := (Real.jacobiDnOfParameter_pos hm u).ne'
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  have h' : HasDerivAt
      (fun v => -((1 / Real.jacobiSnOfParameter v m) * (Real.jacobiDnOfParameter v m /
      Real.jacobiSnOfParameter v m))) _ u :=
    ((Real.hasDerivAt_jacobiNsm hm hs).mul (Real.hasDerivAt_jacobiDsm hm hs)).neg
  have hev : ∀ᶠ v in 𝓝 u, Real.jacobiSnOfParameter v m ≠ 0 :=
    (Real.hasDerivAt_jacobiSnOfParameter hm u).continuousAt.eventually_ne hs
  have hd : deriv (fun u => Real.jacobiCnOfParameter u m / Real.jacobiSnOfParameter u m)
      =ᶠ[𝓝 u] fun v => _ :=
    hev.mono fun v hv => (Real.hasDerivAt_jacobiCsm hm hv).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, h'.deriv]
  field_simp
  linear_combination (-2*(Real.jacobiCnOfParameter u m)) * h1 +
      ((Real.jacobiCnOfParameter u m)) * h2

end RealArgument

end DLMF.JacobiElliptic

end
end
