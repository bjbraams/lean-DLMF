/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Derivatives
public import DLMF.JacobiElliptic.ModulusInversion
public import DLMF.JacobiElliptic.SpecialValues.RealAndHalfPeriods
public import DLMF.Elliptic.JacobiIdentities
public import DLMF.Theta.Products.LogNormIntegral

/-!
# Integrals of the Jacobian elliptic functions (DLMF §22.14)

The indefinite integrals DLMF 22.14.1–22.14.15 of the Jacobian elliptic functions for real `x`,
and the definite logarithmic integrals DLMF 22.14.16–22.14.18, for the modulus `0 < k < 1` and
`k' = √(1 - k²)`.

## Main results

* `Real.hasDerivAt_primitive_jacobiSn`, `Real.hasDerivAt_primitive_jacobiCn`,
  `Real.hasDerivAt_arcsin_jacobiSnOfParameter`: DLMF 22.14.1–22.14.3.
* `Real.hasDerivAt_primitive_jacobiCd`, `Real.hasDerivAt_primitive_jacobiSd`,
  `Real.hasDerivAt_primitive_jacobiNd`: DLMF 22.14.4–22.14.6.
* `Real.hasDerivAt_primitive_jacobiDc`, `Real.hasDerivAt_primitive_jacobiNc`,
  `Real.hasDerivAt_primitive_jacobiSc`: DLMF 22.14.7–22.14.9, for `-K < x < K`.
* `Real.hasDerivAt_primitive_jacobiNs`, `Real.hasDerivAt_primitive_jacobiDs`,
  `Real.hasDerivAt_primitive_jacobiCs`: DLMF 22.14.10–22.14.12, for `0 < x < 2K`.
* `Real.hasDerivAt_primitive_inv_jacobiSn`, `Real.hasDerivAt_primitive_jacobiCn_div_jacobiSn`,
  `Real.hasDerivAt_primitive_jacobiCn_div_jacobiSn_sq`: DLMF 22.14.13–22.14.15.
* `Real.integral_log_jacobiSnOfParameter`, `Real.integral_log_jacobiCnOfParameter`,
  `Real.integral_log_jacobiDnOfParameter`: DLMF 22.14.16–22.14.18.

## Implementation notes

Each indefinite integral is stated as the derivative of the printed primitive,
`HasDerivAt F (pq x) x`, for the real functions `sn = Real.jacobiSnOfParameter x (k²)`, `cn`, `dn`
(the bridge to the complex theta quotients is `jacobiSn_ofReal` and its companions); the nine
quotient functions are written out as quotients.

DLMF's `Arccos` and `Arcsin` in 22.14.2, 22.14.3, 22.14.6 are general (multivalued) inverse
functions. With Mathlib's principal `Real.arccos`, 22.14.2 and 22.14.6 hold on `0 < x < 2K`,
where `sn x > 0` (on `-2K < x < 0` the principal primitive has the opposite sign); in 22.14.3
the primitive `am` has derivative `dn` on all of `ℝ`
(`DLMF.Elliptic.Real.hasDerivAt_jacobiAmOfParameter`) and equals `arcsin (sn x)` on `-K < x < K`,
where the principal form is proved here. The ranges `-K < x < K` (22.14.7–22.14.9) and `0 < x < 2K`
(22.14.10–22.14.15) are DLMF's. The `dn` integral 22.14.18 is proved by quarter-period reflection.
For 22.14.16 the substitution `t = Kθ/π` turns `∫₀^{2K} log sn` into the mean of
`log ‖θ₃(0)θ₁(θ/2)/(θ₂(0)θ₄(θ/2))‖` over a period
(`DLMF.Theta.integral_log_norm_mul_jacobiThetaOneTau_div`); reflection at `K` halves it, and
22.14.17 follows from `cn t = sn(K - t) dn t`.
-/

@[expose] public section

open Real DLMF.Elliptic
open scoped Topology

noncomputable section

namespace DLMF.JacobiElliptic

/-! ### Helper facts about the real amplitude and `sn, cn, dn` -/

section Helpers

variable {m : ℝ}

/-- The amplitude is strictly increasing (helper). -/
theorem strictMono_jacobiAmOfParameter' (hm : m < 1) : StrictMono fun u =>
    Real.jacobiAmOfParameter u m := by
  simp only [Real.jacobiAmOfParameter, hm, ↓reduceDIte]
  exact (Real.incompleteEllipticFOfParameterOrderIso hm).symm.strictMono

/-- `am(2K) = π` (helper). -/
private lemma jacobiAmOfParameter_two_completeEllipticKOfParameter (hm : m < 1) :
    Real.jacobiAmOfParameter (2 * Real.completeEllipticKOfParameter m) m = π := by
  have h := Real.jacobiAmOfParameter_add_two_completeEllipticKOfParameter hm 0
  rwa [zero_add, Real.jacobiAmOfParameter_zero hm, zero_add] at h

/-- `sn x > 0` for `0 < x < 2K` (helper). -/
lemma jacobiSnOfParameter_pos (hm : m < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 2 * Real.completeEllipticKOfParameter m) : 0 < Real.jacobiSnOfParameter x m := by
  have h0 := strictMono_jacobiAmOfParameter' hm hx0
  have h1 := strictMono_jacobiAmOfParameter' hm hx1
  simp only [Real.jacobiAmOfParameter_zero hm,
      jacobiAmOfParameter_two_completeEllipticKOfParameter hm] at h0 h1
  exact Real.sin_pos_of_pos_of_lt_pi h0 h1

/-- `cn x > 0` for `-K < x < K` (helper). -/
private lemma jacobiCnOfParameter_pos (hm : m < 1) {x : ℝ}
    (hx0 : -Real.completeEllipticKOfParameter m < x)
    (hx1 : x < Real.completeEllipticKOfParameter m) : 0 < Real.jacobiCnOfParameter x m := by
  have h0 := strictMono_jacobiAmOfParameter' hm hx0
  have h1 := strictMono_jacobiAmOfParameter' hm hx1
  simp only [Real.jacobiAmOfParameter_neg hm,
      Real.jacobiAmOfParameter_completeEllipticKOfParameter hm] at h0 h1
  exact Real.cos_pos_of_mem_Ioo ⟨h0, h1⟩

/-- `|sn| ≤ 1` and `|cn| ≤ 1` (helper). -/
theorem abs_jacobiSnOfParameter_le_one_and_abs_jacobiCnOfParameter_le_one
    (u : ℝ) : |Real.jacobiSnOfParameter u m| ≤
    1 ∧ |Real.jacobiCnOfParameter u m| ≤ 1 :=
  ⟨Real.abs_sin_le_one _, Real.abs_cos_le_one _⟩

end Helpers

/-! ### §22.14(i): indefinite integrals of the twelve functions -/

section Indefinite

variable {k : ℝ}

/-- DLMF 22.14.1: `∫ sn(x,k) dx = k⁻¹ ln(dn(x,k) - k cn(x,k))`, for all real `x` and
`0 < k < 1`. -/
@[dlmf 22.14.E1 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiSn (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    HasDerivAt (fun x => k⁻¹ *
        Real.log (Real.jacobiDnOfParameter x (k ^ 2) - k * Real.jacobiCnOfParameter x (k ^ 2)))
      (Real.jacobiSnOfParameter x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hd := Real.jacobiDnOfParameter_pos hm x
  have hpos : 0 < Real.jacobiDnOfParameter x (k ^ 2) - k * Real.jacobiCnOfParameter x (k ^ 2) := by
    nlinarith [sq_nonneg
        (Real.jacobiDnOfParameter x (k ^ 2) + k * Real.jacobiCnOfParameter x (k ^ 2))]
  refine ((((Real.hasDerivAt_jacobiDnOfParameter hm x).sub
      ((Real.hasDerivAt_jacobiCnOfParameter hm x).const_mul k)).log
    hpos.ne').const_mul k⁻¹).congr_deriv ?_
  try simp only [Pi.sub_apply]
  field_simp
  ring

/-- DLMF 22.14.2: `∫ cn(x,k) dx = k⁻¹ Arccos(dn(x,k))`, with the principal `arccos`, on
`0 < x < 2K` (where `sn x > 0`). -/
@[dlmf 22.14.E2 "special case: real x, 0 < k < 1, principal arccos on 0 < x < 2K"]
theorem Real.hasDerivAt_primitive_jacobiCn (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 2 * Real.completeEllipticKOfParameter (k ^ 2)) :
    HasDerivAt (fun x => k⁻¹ * Real.arccos (Real.jacobiDnOfParameter x (k ^ 2)))
      (Real.jacobiCnOfParameter x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hd := Real.jacobiDnOfParameter_pos hm x
  have hs := jacobiSnOfParameter_pos hm hx0 hx1
  have hsq : √(1 - Real.jacobiDnOfParameter x (k ^ 2) ^ 2) = k *
      Real.jacobiSnOfParameter x (k ^ 2) := by
    rw [show 1 - Real.jacobiDnOfParameter x (k ^ 2) ^ 2 =
        (k * Real.jacobiSnOfParameter x (k ^ 2)) ^ 2 by
      linear_combination -h2]
    exact Real.sqrt_sq (by positivity)
  have hd1 : Real.jacobiDnOfParameter x (k ^ 2) ≠ 1 := by
    intro h; rw [h] at hsq; simp at hsq; rcases hsq with h | h <;> linarith
  have hdm1 : Real.jacobiDnOfParameter x (k ^ 2) ≠ -1 := by linarith
  refine (((Real.hasDerivAt_arccos hdm1 hd1).comp x
      (Real.hasDerivAt_jacobiDnOfParameter hm x)).const_mul
    k⁻¹).congr_deriv ?_
  rw [hsq]
  field_simp

/-- DLMF 22.14.3: `∫ dn(x,k) dx = Arcsin(sn(x,k))` with the principal `arcsin`
on `-K < x < K`. -/
@[dlmf 22.14.E3 "special case: real x, real parameter m = k² < 1, principal arcsin on |x| < K"]
theorem Real.hasDerivAt_arcsin_jacobiSnOfParameter {m : ℝ} (hm : m < 1) {x : ℝ}
    (hx0 : -Real.completeEllipticKOfParameter m < x)
        (hx1 : x < Real.completeEllipticKOfParameter m) :
    HasDerivAt (fun x => Real.arcsin (Real.jacobiSnOfParameter x m))
        (Real.jacobiDnOfParameter x m) x := by
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hc := jacobiCnOfParameter_pos hm hx0 hx1
  have hsq : √(1 - Real.jacobiSnOfParameter x m ^ 2) = Real.jacobiCnOfParameter x m := by
    rw [show 1 - Real.jacobiSnOfParameter x m ^ 2 = Real.jacobiCnOfParameter x m ^ 2 by
        linear_combination -h1]
    exact Real.sqrt_sq hc.le
  have hs1 : Real.jacobiSnOfParameter x m ≠ 1 := by
    intro h; rw [h] at h1; nlinarith
  have hsm1 : Real.jacobiSnOfParameter x m ≠ -1 := by
    intro h; rw [h] at h1; nlinarith
  refine ((Real.hasDerivAt_arcsin hsm1 hs1).comp x
      (Real.hasDerivAt_jacobiSnOfParameter hm x)).congr_deriv ?_
  rw [hsq]
  field_simp

/-- DLMF 22.14.4: `∫ cd(x,k) dx = k⁻¹ ln(nd(x,k) + k sd(x,k))`, for all real `x`,
`0 < k < 1`. -/
@[dlmf 22.14.E4 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiCd (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    HasDerivAt (fun x => k⁻¹ * Real.log (1 / Real.jacobiDnOfParameter x (k ^ 2) +
        k * (Real.jacobiSnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2))))
      (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hd := Real.jacobiDnOfParameter_pos hm x
  have hs := (abs_jacobiSnOfParameter_le_one_and_abs_jacobiCnOfParameter_le_one (m := k ^ 2) x).1
  have hpos : 0 < 1 + k * Real.jacobiSnOfParameter x (k ^ 2) := by
    have := neg_abs_le (Real.jacobiSnOfParameter x (k ^ 2)); nlinarith
  have hpos' : 0 < 1 / Real.jacobiDnOfParameter x (k ^ 2) +
      k * (Real.jacobiSnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) := by
    rw [mul_div_assoc', ← add_div]; positivity
  refine ((((Real.hasDerivAt_jacobiNdm hm x).add ((Real.hasDerivAt_jacobiSdm hm x).const_mul k)).log
    hpos'.ne').const_mul k⁻¹).congr_deriv ?_
  try simp only [Pi.add_apply]
  field_simp
  linear_combination 0 * h1

/-- DLMF 22.14.5: `∫ sd(x,k) dx = (kk')⁻¹ Arcsin(-k cd(x,k))`, principal `arcsin`, for all
real `x`, `0 < k < 1`. -/
@[dlmf 22.14.E5 "special case: real x, 0 < k < 1, principal arcsin"]
theorem Real.hasDerivAt_primitive_jacobiSd (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    HasDerivAt (fun x => (k * √(1 - k ^ 2))⁻¹ *
        Real.arcsin (-(k * (Real.jacobiCnOfParameter x (k ^ 2) /
            Real.jacobiDnOfParameter x (k ^ 2)))))
      (Real.jacobiSnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hd := Real.jacobiDnOfParameter_pos hm x
  have hkp : 0 < √(1 - k ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hkp2 : √(1 - k ^ 2) ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by linarith)
  have hsq : √(1 - (-(k *
      (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)))) ^ 2) =
      √(1 - k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2) := by
    rw [show 1 - (-(k * (Real.jacobiCnOfParameter x (k ^ 2) /
        Real.jacobiDnOfParameter x (k ^ 2)))) ^ 2 =
        (√(1 - k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) ^ 2 by
      field_simp; linear_combination (-k^2) * h1 + (1) * h2 + (-1) * hkp2]
    exact Real.sqrt_sq (by positivity)
  have hlt : (k * (Real.jacobiCnOfParameter x (k ^ 2) /
      Real.jacobiDnOfParameter x (k ^ 2))) ^ 2 < 1 := by
    have : (k * (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2))) ^ 2 =
        1 - (√(1 - k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) ^ 2 := by
      field_simp; linear_combination (k^2) * h1 + (-1) * h2 + (1) * hkp2
    rw [this]; have : 0 < (√(1 - k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) ^ 2 := by positivity
    linarith
  have hne1 : -(k * (Real.jacobiCnOfParameter x (k ^ 2) /
      Real.jacobiDnOfParameter x (k ^ 2))) ≠ 1 := by
    intro h; rw [← neg_sq, h] at hlt; norm_num at hlt
  have hnem1 : -(k * (Real.jacobiCnOfParameter x (k ^ 2) /
      Real.jacobiDnOfParameter x (k ^ 2))) ≠ -1 := by
    intro h; rw [← neg_sq, h] at hlt; norm_num at hlt
  refine (((Real.hasDerivAt_arcsin hnem1 hne1).comp x
    (((Real.hasDerivAt_jacobiCdm hm x).const_mul k).neg)).const_mul
      (k * √(1 - k ^ 2))⁻¹).congr_deriv ?_
  rw [hsq]
  field_simp
  linear_combination (0) * h1 + (0) * h2 + (-(Real.jacobiSnOfParameter x (k ^ 2))) * hkp2

/-- DLMF 22.14.6: `∫ nd(x,k) dx = k'⁻¹ Arccos(cd(x,k))`, principal `arccos`, on `0 < x < 2K`. -/
@[dlmf 22.14.E6 "special case: real x, 0 < k < 1, principal arccos on 0 < x < 2K"]
theorem Real.hasDerivAt_primitive_jacobiNd (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 2 * Real.completeEllipticKOfParameter (k ^ 2)) :
    HasDerivAt (fun x => (√(1 - k ^ 2))⁻¹ *
        Real.arccos (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)))
      (1 / Real.jacobiDnOfParameter x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hd := Real.jacobiDnOfParameter_pos hm x
  have hs := jacobiSnOfParameter_pos hm hx0 hx1
  have hkp : 0 < √(1 - k ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hkp2 : √(1 - k ^ 2) ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by linarith)
  have hsq : √(1 - (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) ^ 2) =
      √(1 - k ^ 2) * Real.jacobiSnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2) := by
    rw [show 1 - (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) ^ 2 =
        (√(1 - k ^ 2) * Real.jacobiSnOfParameter x (k ^ 2) /
            Real.jacobiDnOfParameter x (k ^ 2)) ^ 2 by
      field_simp; linear_combination (-k^2 - √(1 - k ^ 2)^2) * h1 + (1) * h2 +
          ((Real.jacobiCnOfParameter x (k ^ 2))^2 - 1) * hkp2]
    exact Real.sqrt_sq (by positivity)
  have hlt : (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) ^ 2 < 1 := by
    have : (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2)) ^ 2 =
        1 - (√(1 - k ^ 2) * Real.jacobiSnOfParameter x (k ^ 2) /
            Real.jacobiDnOfParameter x (k ^ 2)) ^ 2 := by
      field_simp; linear_combination (k^2 + √(1 - k ^ 2)^2) * h1 + (-1) * h2 + (1 -
          (Real.jacobiCnOfParameter x (k ^ 2))^2) * hkp2
    rw [this]
    have : 0 < (√(1 - k ^ 2) * Real.jacobiSnOfParameter x (k ^ 2) /
        Real.jacobiDnOfParameter x (k ^ 2)) ^ 2 := by
      positivity
    linarith
  have hne1 : Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2) ≠ 1 := by
    intro h; rw [h] at hlt; norm_num at hlt
  have hnem1 : Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiDnOfParameter x (k ^ 2) ≠ -1 := by
    intro h; rw [h] at hlt; norm_num at hlt
  refine (((Real.hasDerivAt_arccos hnem1 hne1).comp x (Real.hasDerivAt_jacobiCdm hm x)).const_mul
    (√(1 - k ^ 2))⁻¹).congr_deriv ?_
  rw [hsq]
  field_simp
  linear_combination (0) * h1 + (0) * h2 + (-1) * hkp2

/-- DLMF 22.14.7: `∫ dc(x,k) dx = ln(nc(x,k) + sc(x,k))` for `-K < x < K`. -/
@[dlmf 22.14.E7 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiDc (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.completeEllipticKOfParameter (k ^ 2) < x)
        (hx1 : x < Real.completeEllipticKOfParameter (k ^ 2)) :
    HasDerivAt (fun x => Real.log (1 / Real.jacobiCnOfParameter x (k ^ 2) +
        Real.jacobiSnOfParameter x (k ^ 2) / Real.jacobiCnOfParameter x (k ^ 2)))
      (Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiCnOfParameter x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hc := jacobiCnOfParameter_pos hm hx0 hx1
  have hs : 0 < 1 + Real.jacobiSnOfParameter x (k ^ 2) := by
    nlinarith [sq_nonneg (1 + Real.jacobiSnOfParameter x (k ^ 2))]
  have hpos : 0 < 1 / Real.jacobiCnOfParameter x (k ^ 2) +
      Real.jacobiSnOfParameter x (k ^ 2) / Real.jacobiCnOfParameter x (k ^ 2) := by
    rw [← add_div]; positivity
  refine (((Real.hasDerivAt_jacobiNcm hm hc.ne').add (Real.hasDerivAt_jacobiScm hm hc.ne')).log
    hpos.ne').congr_deriv ?_
  try simp only [Pi.add_apply]
  field_simp
  linear_combination 0 * h1

/-- DLMF 22.14.8: `∫ nc(x,k) dx = k'⁻¹ ln(dc(x,k) + k' sc(x,k))` for `-K < x < K`. -/
@[dlmf 22.14.E8 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiNc (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.completeEllipticKOfParameter (k ^ 2) < x)
        (hx1 : x < Real.completeEllipticKOfParameter (k ^ 2)) :
    HasDerivAt (fun x => (√(1 - k ^ 2))⁻¹ * Real.log (Real.jacobiDnOfParameter x (k ^ 2) /
        Real.jacobiCnOfParameter x (k ^ 2) + √(1 - k ^ 2) * (Real.jacobiSnOfParameter x (k ^ 2) /
          Real.jacobiCnOfParameter x (k ^ 2))))
      (1 / Real.jacobiCnOfParameter x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hc := jacobiCnOfParameter_pos hm hx0 hx1
  have hd := Real.jacobiDnOfParameter_pos hm x
  have hkp : 0 < √(1 - k ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hkp2 : √(1 - k ^ 2) ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by linarith)
  have hnum : 0 < Real.jacobiDnOfParameter x (k ^ 2) + √(1 - k ^ 2) *
      Real.jacobiSnOfParameter x (k ^ 2) := by
    have hsq : (Real.jacobiDnOfParameter x (k ^ 2) - √(1 - k ^ 2) *
        Real.jacobiSnOfParameter x (k ^ 2)) *
        (Real.jacobiDnOfParameter x (k ^ 2) + √(1 - k ^ 2) * Real.jacobiSnOfParameter x (k ^ 2)) =
          Real.jacobiCnOfParameter x (k ^ 2) ^ 2 := by
      linear_combination (-k^2 - √(1 - k ^ 2)^2) * h1 + (1) * h2 +
          ((Real.jacobiCnOfParameter x (k ^ 2))^2 -
          1) * hkp2
    nlinarith [sq_pos_of_pos hc]
  have hpos : 0 < Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiCnOfParameter x (k ^ 2) +
      √(1 - k ^ 2) * (Real.jacobiSnOfParameter x (k ^ 2) / Real.jacobiCnOfParameter x (k ^ 2)) := by
    rw [mul_div_assoc', ← add_div]; positivity
  refine ((((Real.hasDerivAt_jacobiDcm hm hc.ne').add
    ((Real.hasDerivAt_jacobiScm hm hc.ne').const_mul
    √(1 - k ^ 2))).log hpos.ne').const_mul (√(1 - k ^ 2))⁻¹).congr_deriv ?_
  try simp only [Pi.add_apply]
  field_simp
  linear_combination (0) * h1 + (0) * h2 + (-(Real.jacobiSnOfParameter x (k ^ 2))) * hkp2

/-- DLMF 22.14.9: `∫ sc(x,k) dx = k'⁻¹ ln(dc(x,k) + k' nc(x,k))` for `-K < x < K`. -/
@[dlmf 22.14.E9 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiSc (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.completeEllipticKOfParameter (k ^ 2) < x)
        (hx1 : x < Real.completeEllipticKOfParameter (k ^ 2)) :
    HasDerivAt (fun x => (√(1 - k ^ 2))⁻¹ * Real.log (Real.jacobiDnOfParameter x (k ^ 2) /
        Real.jacobiCnOfParameter x (k ^ 2) + √(1 - k ^ 2) *
            (1 / Real.jacobiCnOfParameter x (k ^ 2))))
      (Real.jacobiSnOfParameter x (k ^ 2) / Real.jacobiCnOfParameter x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hc := jacobiCnOfParameter_pos hm hx0 hx1
  have hd := Real.jacobiDnOfParameter_pos hm x
  have hkp : 0 < √(1 - k ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hkp2 : √(1 - k ^ 2) ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by linarith)
  have hpos : 0 < Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiCnOfParameter x (k ^ 2) +
      √(1 - k ^ 2) * (1 / Real.jacobiCnOfParameter x (k ^ 2)) := by positivity
  refine ((((Real.hasDerivAt_jacobiDcm hm hc.ne').add
    ((Real.hasDerivAt_jacobiNcm hm hc.ne').const_mul
    √(1 - k ^ 2))).log hpos.ne').const_mul (√(1 - k ^ 2))⁻¹).congr_deriv ?_
  have hn : Real.jacobiDnOfParameter x (k ^ 2) + √(1 - k ^ 2) ≠ 0 := by positivity
  try simp only [Pi.add_apply]
  field_simp
  linear_combination (0) * h1 + (0) * h2 + (-(Real.jacobiSnOfParameter x (k ^ 2))) * hkp2

/-- DLMF 22.14.10: `∫ ns(x,k) dx = ln(ds(x,k) - cs(x,k))` for `0 < x < 2K`. -/
@[dlmf 22.14.E10 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiNs (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 2 * Real.completeEllipticKOfParameter (k ^ 2)) :
    HasDerivAt (fun x =>
        Real.log (Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2) -
        Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2)))
      (1 / Real.jacobiSnOfParameter x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hs := jacobiSnOfParameter_pos hm hx0 hx1
  have hd := Real.jacobiDnOfParameter_pos hm x
  have hdc : 0 < Real.jacobiDnOfParameter x (k ^ 2) - Real.jacobiCnOfParameter x (k ^ 2) := by
    have hsq : (Real.jacobiDnOfParameter x (k ^ 2) - Real.jacobiCnOfParameter x (k ^ 2)) *
        (Real.jacobiDnOfParameter x (k ^ 2) + Real.jacobiCnOfParameter x (k ^ 2)) =
          (1 - k ^ 2) * Real.jacobiSnOfParameter x (k ^ 2) ^ 2 := by linear_combination h2 - h1
    have : 0 < (1 - k ^ 2) * Real.jacobiSnOfParameter x (k ^ 2) ^ 2 := by
      have : 0 < 1 - k ^ 2 := by linarith
      positivity
    nlinarith
  have hpos : 0 < Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2) -
      Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2) := by
    rw [← sub_div]; positivity
  refine (((Real.hasDerivAt_jacobiDsm hm hs.ne').sub (Real.hasDerivAt_jacobiCsm hm hs.ne')).log
    hpos.ne').congr_deriv ?_
  have hdc' := hdc.ne'
  try simp only [Pi.sub_apply]
  field_simp
  linear_combination 0 * h1

/-- DLMF 22.14.11: `∫ ds(x,k) dx = ln(ns(x,k) - cs(x,k))` for `0 < x < 2K`. -/
@[dlmf 22.14.E11 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiDs (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 2 * Real.completeEllipticKOfParameter (k ^ 2)) :
    HasDerivAt (fun x => Real.log (1 / Real.jacobiSnOfParameter x (k ^ 2) -
        Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2)))
      (Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hs := jacobiSnOfParameter_pos hm hx0 hx1
  have hc1 : 0 < 1 - Real.jacobiCnOfParameter x (k ^ 2) := by nlinarith [sq_pos_of_pos hs]
  have hpos : 0 < 1 / Real.jacobiSnOfParameter x (k ^ 2) -
      Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2) := by
    rw [← sub_div]; positivity
  refine (((Real.hasDerivAt_jacobiNsm hm hs.ne').sub (Real.hasDerivAt_jacobiCsm hm hs.ne')).log
    hpos.ne').congr_deriv ?_
  have hc1' := hc1.ne'
  try simp only [Pi.sub_apply]
  field_simp
  linear_combination 0 * h1

/-- DLMF 22.14.12: `∫ cs(x,k) dx = ln(ns(x,k) - ds(x,k))` for `0 < x < 2K`. -/
@[dlmf 22.14.E12 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiCs (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 2 * Real.completeEllipticKOfParameter (k ^ 2)) :
    HasDerivAt (fun x => Real.log (1 / Real.jacobiSnOfParameter x (k ^ 2) -
        Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2)))
      (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hs := jacobiSnOfParameter_pos hm hx0 hx1
  have hd := Real.jacobiDnOfParameter_pos hm x
  have hd1 : 0 < 1 - Real.jacobiDnOfParameter x (k ^ 2) := by
    have : 0 < k ^ 2 * Real.jacobiSnOfParameter x (k ^ 2) ^ 2 := by positivity
    nlinarith
  have hpos : 0 < 1 / Real.jacobiSnOfParameter x (k ^ 2) -
      Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2) := by
    rw [← sub_div]; positivity
  refine (((Real.hasDerivAt_jacobiNsm hm hs.ne').sub (Real.hasDerivAt_jacobiDsm hm hs.ne')).log
    hpos.ne').congr_deriv ?_
  have hd1' := hd1.ne'
  try simp only [Pi.sub_apply]
  field_simp
  linear_combination 0 * h1

end Indefinite

/-! ### §22.14(iii): other indefinite integrals -/

section Other

variable {k : ℝ}

/-- DLMF 22.14.13: `∫ dx/sn(x,k) = ln(sn(x,k)/(cn(x,k) + dn(x,k)))` for `0 < x < 2K`. -/
@[dlmf 22.14.E13 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_inv_jacobiSn (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 2 * Real.completeEllipticKOfParameter (k ^ 2)) :
    HasDerivAt (fun x => Real.log (Real.jacobiSnOfParameter x (k ^ 2) /
        (Real.jacobiCnOfParameter x (k ^ 2) + Real.jacobiDnOfParameter x (k ^ 2))))
      (1 / Real.jacobiSnOfParameter x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hs := jacobiSnOfParameter_pos hm hx0 hx1
  have hd := Real.jacobiDnOfParameter_pos hm x
  have hcd : 0 < Real.jacobiCnOfParameter x (k ^ 2) + Real.jacobiDnOfParameter x (k ^ 2) := by
    have hsq : (Real.jacobiDnOfParameter x (k ^ 2) - Real.jacobiCnOfParameter x (k ^ 2)) *
        (Real.jacobiDnOfParameter x (k ^ 2) + Real.jacobiCnOfParameter x (k ^ 2)) =
          (1 - k ^ 2) * Real.jacobiSnOfParameter x (k ^ 2) ^ 2 := by linear_combination h2 - h1
    have : 0 < (1 - k ^ 2) * Real.jacobiSnOfParameter x (k ^ 2) ^ 2 := by
      have : 0 < 1 - k ^ 2 := by linarith
      positivity
    nlinarith
  have hpos : 0 < Real.jacobiSnOfParameter x (k ^ 2) /
      (Real.jacobiCnOfParameter x (k ^ 2) + Real.jacobiDnOfParameter x (k ^ 2)) := by positivity
  refine (((Real.hasDerivAt_jacobiSnOfParameter hm x).div
      ((Real.hasDerivAt_jacobiCnOfParameter hm x).add
    (Real.hasDerivAt_jacobiDnOfParameter hm x)) hcd.ne').log hpos.ne').congr_deriv ?_
  try simp only [Pi.add_apply, Pi.div_apply]
  field_simp
  linear_combination ((Real.jacobiDnOfParameter x (k ^ 2))) * h1 +
      ((Real.jacobiCnOfParameter x (k ^ 2))) * h2

/-- DLMF 22.14.14: `∫ cn(x,k)/sn(x,k) dx = ½ ln((1 - dn(x,k))/(1 + dn(x,k)))` for
`0 < x < 2K`. -/
@[dlmf 22.14.E14 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiCn_div_jacobiSn (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 2 * Real.completeEllipticKOfParameter (k ^ 2)) :
    HasDerivAt (fun x => 1 / 2 * Real.log ((1 - Real.jacobiDnOfParameter x (k ^ 2)) /
        (1 + Real.jacobiDnOfParameter x (k ^ 2))))
      (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hs := jacobiSnOfParameter_pos hm hx0 hx1
  have hd := Real.jacobiDnOfParameter_pos hm x
  have hd1 : 0 < 1 - Real.jacobiDnOfParameter x (k ^ 2) := by
    have : 0 < k ^ 2 * Real.jacobiSnOfParameter x (k ^ 2) ^ 2 := by positivity
    nlinarith
  have hpos : 0 < (1 - Real.jacobiDnOfParameter x (k ^ 2)) /
      (1 + Real.jacobiDnOfParameter x (k ^ 2)) := by
    positivity
  refine (((((Real.hasDerivAt_jacobiDnOfParameter hm x).const_sub 1).div
    ((Real.hasDerivAt_jacobiDnOfParameter hm x).const_add 1) (by positivity)).log
        hpos.ne').const_mul
      (1 / 2)).congr_deriv ?_
  have hd1' := hd1.ne'
  try simp only [Pi.div_apply]
  field_simp
  linear_combination (0) * h1 + (2*(Real.jacobiCnOfParameter x (k ^ 2))) * h2

/-- DLMF 22.14.15: `∫ cn(x,k)/sn²(x,k) dx = -dn(x,k)/sn(x,k)` for `0 < x < 2K`. -/
@[dlmf 22.14.E15 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiCn_div_jacobiSn_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 2 * Real.completeEllipticKOfParameter (k ^ 2)) :
    HasDerivAt (fun x => -(Real.jacobiDnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2)))
      (Real.jacobiCnOfParameter x (k ^ 2) / Real.jacobiSnOfParameter x (k ^ 2) ^ 2) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm x
  have hs := jacobiSnOfParameter_pos hm hx0 hx1
  refine (((Real.hasDerivAt_jacobiDnOfParameter hm x).div
      (Real.hasDerivAt_jacobiSnOfParameter hm x) hs.ne').neg
    ).congr_deriv ?_
  field_simp
  linear_combination (0) * h1 + ((Real.jacobiCnOfParameter x (k ^ 2))) * h2

end Other

/-! ### §22.14(iv): definite integrals -/

section Definite

variable {k : ℝ}

/-- DLMF 22.14.18: `∫₀^K ln dn(t,k) dt = K(k) ln(k')/2`, `0 < k < 1`. -/
@[dlmf 22.14.E18 "special case: 0 < k < 1"]
theorem Real.integral_log_jacobiDnOfParameter (hk0 : 0 < k) (hk1 : k < 1) :
    ∫ t in (0 : ℝ)..Real.completeEllipticKOfParameter (k ^ 2),
        Real.log (Real.jacobiDnOfParameter t (k ^ 2)) =
      1 / 2 * Real.completeEllipticKOfParameter (k ^ 2) * Real.log (√(1 - k ^ 2)) := by
  have hm : k ^ 2 < 1 := by nlinarith
  let K := Real.completeEllipticKOfParameter (k ^ 2)
  have hc : Continuous (fun t => Real.log (Real.jacobiDnOfParameter t (k ^ 2))) := by
    apply Continuous.log
    · exact continuous_iff_continuousAt.mpr fun t =>
        (Real.hasDerivAt_jacobiDnOfParameter hm t).continuousAt
    · exact fun t => (Real.jacobiDnOfParameter_pos hm t).ne'
  have hshift (t : ℝ) : Real.log (Real.jacobiDnOfParameter (K - t) (k ^ 2)) =
      Real.log (√(1 - k ^ 2)) - Real.log (Real.jacobiDnOfParameter t (k ^ 2)) := by
    have h := (Real.jacobi_add_completeEllipticKOfParameter hm (-t)).2.2
    rw [(jacobi_neg hm t).2.2] at h
    have h' : Real.jacobiDnOfParameter (K - t) (k ^ 2) =
        √(1 - k ^ 2) / Real.jacobiDnOfParameter t (k ^ 2) := by
      simpa only [Real.sqrt_eq_rpow, sub_eq_add_neg, add_comm] using h
    rw [h', Real.log_div (Real.sqrt_pos.mpr (by linarith)).ne'
      (Real.jacobiDnOfParameter_pos hm t).ne']
  have he := intervalIntegral.integral_comp_sub_left
    (fun t => Real.log (Real.jacobiDnOfParameter t (k ^ 2))) (a := 0) (b := K) K
  simp only [sub_self, sub_zero] at he
  simp_rw [hshift] at he
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable 0 K),
    intervalIntegral.integral_const] at he
  simp only [sub_zero, smul_eq_mul] at he
  change _ = 1 / 2 * K * Real.log (√(1 - k ^ 2))
  linarith

open Complex MeasureTheory DLMF.Theta DLMF.EllipticIntegrals in
/-- `∫₀^{2K} log sn(t,k) dt = -K ln k - π K'/2`, with integrability (`0 < k < 1`). -/
private lemma integral_log_jacobiSnOfParameter_two_completeEllipticKOfParameter (hk0 : 0 < k)
    (hk1 : k < 1) :
    IntervalIntegrable (fun t => Real.log (Real.jacobiSnOfParameter t (k ^ 2))) volume 0
        (2 * Real.completeEllipticKOfParameter (k ^ 2)) ∧
      ∫ t in (0 : ℝ)..2 * Real.completeEllipticKOfParameter (k ^ 2),
          Real.log (Real.jacobiSnOfParameter t (k ^ 2)) =
        -(Real.completeEllipticKOfParameter (k ^ 2) * Real.log k) - π *
            Real.completeEllipticKOfParameter (1 - k ^ 2) / 2 := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hdom : (k : ℂ) ∈ jacobiModulusDomain := ⟨by simpa using hk0, fun _ => by simpa using hk1⟩
  set τ := jacobiTau k with hτdef
  have hτ : 0 < τ.im := jacobiTau_im_pos hdom
  set K := Real.completeEllipticKOfParameter (k ^ 2) with hKdef
  set K' := Real.completeEllipticKOfParameter (1 - k ^ 2) with hK'def
  have hK : completeEllipticK k = (K : ℂ) := completeEllipticK_ofReal hm
  have hK' : completeEllipticKPrime k = (K' : ℂ) := completeEllipticKPrime_ofReal (by positivity)
  have hKpos : 0 < K := Real.completeEllipticKOfParameter_pos hm
  have hK0 : (K : ℂ) ≠ 0 := ofReal_ne_zero.mpr hKpos.ne'
  have hτim : τ.im = K' / K := by
    rw [hτdef, jacobiTau, hK, hK']
    rw [show I * (K' : ℂ) / K = ((K' / K : ℝ) : ℂ) * I by push_cast; ring, mul_I_im, ofReal_re]
  set C := jacobiThetaThreeTau 0 τ / jacobiThetaTwoTau 0 τ with hCdef
  have h2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have h3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have h4 := jacobiThetaFourTau_zero_ne_zero hτ
  have hC : C ≠ 0 := div_ne_zero h3 h2
  -- the integrand in the variable `θ = π t/K`
  have hsn : ∀ θ : ℝ, Real.log (Real.jacobiSnOfParameter (K / π * θ) (k ^ 2)) =
      Real.log ‖C * (jacobiThetaOneTau ((θ / 2 : ℝ) : ℂ) τ /
        jacobiThetaFourTau ((θ / 2 : ℝ) : ℂ) τ)‖ := by
    intro θ
    rw [← Real.log_abs, ← Real.norm_eq_abs, ← Complex.norm_real, ← jacobiSn_ofReal hk0 hk1]
    congr 2
    have hz : jacobiThetaArgument ((K / π * θ : ℝ) : ℂ) k = ((θ / 2 : ℝ) : ℂ) := by
      rw [jacobiThetaArgument, hK]
      have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast
      field_simp
    simp only [jacobiSn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq,
      ↓reduceIte, hz, ← hτdef]
    rw [hCdef]
    rw [div_div_eq_mul_div]
    field_simp
  obtain ⟨hint, hval⟩ := integral_log_norm_mul_jacobiThetaOneTau_div hτ hC
  have hπ : (0 : ℝ) < π := Real.pi_pos
  -- `log ‖C‖ = -(1/2) log k`
  have hmod := (jacobi_inversion_k hdom).1
  rw [jacobiModulusOfTau, ← hτdef] at hmod
  have hCsq : C ^ 2 = ((1 / k : ℝ) : ℂ) := by
    rw [hCdef, div_pow, Complex.ofReal_div, Complex.ofReal_one, ← hmod]
    field_simp
  have hlogC : Real.log ‖C‖ = -(1 / 2 * Real.log k) := by
    have h := congrArg (fun z : ℂ => Real.log ‖z‖) hCsq
    simp only [norm_pow, Real.log_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hk0), Real.log_div one_ne_zero hk0.ne', Real.log_one] at h
    push_cast at h
    linarith
  have hg : (fun t => Real.log (Real.jacobiSnOfParameter t (k ^ 2))) =
      fun t => Real.log ‖C * (jacobiThetaOneTau (((π / K * t) / 2 : ℝ) : ℂ) τ /
        jacobiThetaFourTau (((π / K * t) / 2 : ℝ) : ℂ) τ)‖ := by
    funext t
    rw [← hsn]
    congr 2
    field_simp
  refine ⟨?_, ?_⟩
  · have h := hint.comp_mul_left (c := π / K)
    rw [zero_div, show 2 * π / (π / K) = 2 * K by field_simp] at h
    rw [hg]
    exact h
  · have h := intervalIntegral.integral_comp_mul_left
      (fun t => Real.log (Real.jacobiSnOfParameter t (k ^ 2))) (c := K / π) (a := 0) (b := 2 * π)
      (div_ne_zero hKpos.ne' hπ.ne')
    simp only [hsn] at h
    rw [hval, mul_zero, show K / π * (2 * π) = 2 * K by field_simp, smul_eq_mul] at h
    have hI : ∫ t in (0 : ℝ)..2 * K, Real.log (Real.jacobiSnOfParameter t (k ^ 2)) =
        K / π * (2 * π * (Real.log ‖C‖ - π * τ.im / 4)) := by
      rw [h, ← mul_assoc, mul_inv_cancel₀ (div_ne_zero hKpos.ne' hπ.ne'), one_mul]
    rw [hI, hlogC, hτim]
    field_simp
    ring

open Complex MeasureTheory DLMF.Theta DLMF.EllipticIntegrals in
/-- Quarter-period reflection: `∫₀^K log sn = ∫_K^{2K} log sn`, with the integrability on
`[0, K]` (helper). -/
private lemma integral_log_jacobiSnOfParameter_completeEllipticKOfParameter (hk0 : 0 < k)
    (hk1 : k < 1) :
    IntervalIntegrable (fun t => Real.log (Real.jacobiSnOfParameter t (k ^ 2))) volume 0
        (Real.completeEllipticKOfParameter (k ^ 2)) ∧
      ∫ t in (0 : ℝ)..Real.completeEllipticKOfParameter (k ^ 2),
          Real.log (Real.jacobiSnOfParameter t (k ^ 2)) =
        -(π / 4) * Real.completeEllipticKOfParameter (1 - k ^ 2) -
          1 / 2 * Real.completeEllipticKOfParameter (k ^ 2) * Real.log k := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨hint, hval⟩ := integral_log_jacobiSnOfParameter_two_completeEllipticKOfParameter hk0 hk1
  set K := Real.completeEllipticKOfParameter (k ^ 2) with hKdef
  have hKpos : 0 < K := Real.completeEllipticKOfParameter_pos hm
  set g := fun t => Real.log (Real.jacobiSnOfParameter t (k ^ 2)) with hg
  have h1 : IntervalIntegrable g volume 0 K := hint.mono_set (by
    rw [Set.uIcc_of_le hKpos.le, Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc le_rfl (by linarith))
  have h2 : IntervalIntegrable g volume K (2 * K) := hint.mono_set (by
    rw [Set.uIcc_of_le (by linarith : K ≤ 2 * K), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc hKpos.le le_rfl)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hrefl : ∀ x, g (K + x) = g (K - x) := by
    intro x
    simp only [hg]
    rw [add_comm, sub_eq_add_neg, add_comm K (-x),
        (Real.jacobi_add_completeEllipticKOfParameter hm x).1,
      (Real.jacobi_add_completeEllipticKOfParameter hm (-x)).1, (jacobi_neg hm x).2.1,
          (jacobi_neg hm x).2.2]
  have hsym : ∫ t in K..2 * K, g t = ∫ t in (0 : ℝ)..K, g t := by
    have ha := intervalIntegral.integral_comp_add_left g (a := 0) (b := K) K
    have hs := intervalIntegral.integral_comp_sub_left g (a := 0) (b := K) K
    simp only [add_zero, sub_self, sub_zero] at ha hs
    rw [show K + K = 2 * K by ring] at ha
    rw [← ha, ← hs]
    exact intervalIntegral.integral_congr fun x _ => hrefl x
  refine ⟨h1, ?_⟩
  rw [hsym] at hsplit
  change ∫ t in (0 : ℝ)..K, g t = _
  linarith

/-- DLMF 22.14.16: `∫₀^K ln sn(t,k) dt = -π K'(k)/4 - K(k) ln(k)/2`, `0 < k < 1`, with
`K = K(k²)`, `K' = K(1 - k²)` in the parameter convention. -/
@[dlmf 22.14.E16 "special case: 0 < k < 1"]
theorem Real.integral_log_jacobiSnOfParameter (hk0 : 0 < k) (hk1 : k < 1) :
    ∫ t in (0 : ℝ)..Real.completeEllipticKOfParameter (k ^ 2),
        Real.log (Real.jacobiSnOfParameter t (k ^ 2)) =
      -(π / 4) * Real.completeEllipticKOfParameter (1 - k ^ 2) - 1 / 2 *
          Real.completeEllipticKOfParameter (k ^ 2) * Real.log k :=
          by
  exact (integral_log_jacobiSnOfParameter_completeEllipticKOfParameter hk0 hk1).2

open MeasureTheory in
/-- DLMF 22.14.17: `∫₀^K ln cn(t,k) dt = -π K'(k)/4 + K(k) ln(k'/k)/2`, `0 < k < 1`. -/
@[dlmf 22.14.E17 "special case: 0 < k < 1"]
theorem Real.integral_log_jacobiCnOfParameter (hk0 : 0 < k) (hk1 : k < 1) :
    ∫ t in (0 : ℝ)..Real.completeEllipticKOfParameter (k ^ 2),
        Real.log (Real.jacobiCnOfParameter t (k ^ 2)) =
      -(π / 4) * Real.completeEllipticKOfParameter (1 - k ^ 2) +
        1 / 2 * Real.completeEllipticKOfParameter (k ^ 2) * Real.log (√(1 - k ^ 2) / k) := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, hs⟩ := integral_log_jacobiSnOfParameter_completeEllipticKOfParameter hk0 hk1
  have hd := Real.integral_log_jacobiDnOfParameter hk0 hk1
  set K := Real.completeEllipticKOfParameter (k ^ 2) with hKdef
  have hKpos : 0 < K := Real.completeEllipticKOfParameter_pos hm
  have hc : Continuous (fun t => Real.log (Real.jacobiDnOfParameter t (k ^ 2))) := by
    apply Continuous.log
    · exact continuous_iff_continuousAt.mpr fun t =>
        (Real.hasDerivAt_jacobiDnOfParameter hm t).continuousAt
    · exact fun t => (Real.jacobiDnOfParameter_pos hm t).ne'
  have h1' : IntervalIntegrable
      (fun t => Real.log (Real.jacobiSnOfParameter (K - t) (k ^ 2))) volume 0
      K := by
    have := h1.comp_sub_left K
    simp only [sub_zero, sub_self] at this
    exact this.symm
  have heq : Set.EqOn (fun t => Real.log (Real.jacobiSnOfParameter (K - t) (k ^ 2)) +
      Real.log (Real.jacobiDnOfParameter t (k ^ 2)))
      (fun t => Real.log (Real.jacobiCnOfParameter t (k ^ 2))) (Set.uIoo 0 K) := by
    intro t ht
    rw [Set.uIoo_of_le hKpos.le] at ht
    obtain ⟨ht0, ht1⟩ := ht
    have hsn : Real.jacobiSnOfParameter (K - t) (k ^ 2) =
        Real.jacobiCnOfParameter t (k ^ 2) / Real.jacobiDnOfParameter t (k ^ 2) := by
      rw [sub_eq_add_neg, add_comm, (Real.jacobi_add_completeEllipticKOfParameter hm (-t)).1,
        (jacobi_neg hm t).2.1, (jacobi_neg hm t).2.2]
    have hpos : 0 < Real.jacobiSnOfParameter (K - t) (k ^ 2) :=
      jacobiSnOfParameter_pos hm (by linarith) (by linarith)
    have hdpos := Real.jacobiDnOfParameter_pos hm t
    simp only
    rw [← Real.log_mul hpos.ne' hdpos.ne', hsn, div_mul_cancel₀ _ hdpos.ne']
  rw [← intervalIntegral.integral_congr_uIoo heq,
    intervalIntegral.integral_add h1' (hc.intervalIntegrable 0 K)]
  have hr := intervalIntegral.integral_comp_sub_left
    (fun t => Real.log (Real.jacobiSnOfParameter t (k ^ 2))) (a := 0) (b := K) K
  simp only [sub_zero, sub_self] at hr
  rw [hr, hs, hd, Real.log_div (Real.sqrt_pos.mpr (by linarith)).ne' hk0.ne']
  ring

end Definite

end DLMF.JacobiElliptic
