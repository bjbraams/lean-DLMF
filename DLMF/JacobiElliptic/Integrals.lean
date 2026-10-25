/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Derivatives
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Integrals of the Jacobian elliptic functions (DLMF §22.14)

DLMF 22.14.1–22.14.15 are indefinite integrals for real `x`. Each is stated as the
derivative of the printed primitive, `HasDerivAt F (pq x) x`, for the existing real functions
`sn = Real.jacobiSnm x (k²)`, `cn`, `dn` (the bridge to the complex theta quotients is
`jacobiSnk_ofReal` etc. in `DLMF.JacobiElliptic.SpecialValues`) with the modulus `0 < k < 1` and
`k' = √(1 - k²)`; the nine quotient functions are written out as quotients. All fifteen are
proved.

DLMF's `Arccos` and `Arcsin` in 22.14.2, 22.14.3, 22.14.6 are general (multivalued) inverse
functions. With Mathlib's principal `Real.arccos`, 22.14.2 and 22.14.6 hold on
`0 < x < 2K`, where `sn x > 0` (on `-2K < x < 0` the principal primitive has the opposite
sign); in 22.14.3 the primitive `am` has derivative `dn` on all of `ℝ`
(`DLMF.Elliptic.Real.hasDerivAt_jacobiAmm`) and equals `arcsin (sn x)` on `-K < x < K`, where the
principal form is proved here. The ranges `-K < x < K` (22.14.7–22.14.9) and
`0 < x < 2K` (22.14.10–22.14.15) are DLMF's.

The definite integrals 22.14.16–22.14.18 of `ln sn`, `ln cn`, `ln dn` over `[0, K]` are
admitted.
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
lemma je22b_jacobiAmm_strictMono (hm : m < 1) : StrictMono fun u => Real.jacobiAmm u m := by
  simp only [Real.jacobiAmm, hm, ↓reduceDIte]
  exact (Real.incEllIntFmOrderIso hm).symm.strictMono

/-- `am(2K) = π` (helper). -/
lemma je22b_jacobiAmm_two_compEllIntKm (hm : m < 1) :
    Real.jacobiAmm (2 * Real.compEllIntKm m) m = π := by
  have h := Real.jacobiAmm_add_two_compEllIntKm hm 0
  rwa [zero_add, Real.jacobiAmm_zero hm, zero_add] at h

/-- `sn x > 0` for `0 < x < 2K` (helper). -/
lemma je22b_jacobiSnm_pos (hm : m < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 2 * Real.compEllIntKm m) : 0 < Real.jacobiSnm x m := by
  have h0 := je22b_jacobiAmm_strictMono hm hx0
  have h1 := je22b_jacobiAmm_strictMono hm hx1
  simp only [Real.jacobiAmm_zero hm, je22b_jacobiAmm_two_compEllIntKm hm] at h0 h1
  exact Real.sin_pos_of_pos_of_lt_pi h0 h1

/-- `cn x > 0` for `-K < x < K` (helper). -/
lemma je22b_jacobiCnm_pos (hm : m < 1) {x : ℝ} (hx0 : -Real.compEllIntKm m < x)
    (hx1 : x < Real.compEllIntKm m) : 0 < Real.jacobiCnm x m := by
  have h0 := je22b_jacobiAmm_strictMono hm hx0
  have h1 := je22b_jacobiAmm_strictMono hm hx1
  simp only [Real.jacobiAmm_neg hm, Real.jacobiAmm_compEllIntKm hm] at h0 h1
  exact Real.cos_pos_of_mem_Ioo ⟨h0, h1⟩

/-- `|sn| ≤ 1` and `|cn| ≤ 1` (helper). -/
lemma je22b_abs_le_one (u : ℝ) : |Real.jacobiSnm u m| ≤ 1 ∧ |Real.jacobiCnm u m| ≤ 1 :=
  ⟨Real.abs_sin_le_one _, Real.abs_cos_le_one _⟩

end Helpers

/-! ### §22.14(i): indefinite integrals of the twelve functions -/

section Indefinite

variable {k : ℝ}

/-- DLMF 22.14.1: `∫ sn(x,k) dx = k⁻¹ ln(dn(x,k) - k cn(x,k))`, for all real `x` and
`0 < k < 1`. -/
@[dlmf 22.14.E1 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiSn (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    HasDerivAt (fun x => k⁻¹ * Real.log (Real.jacobiDnm x (k ^ 2) - k * Real.jacobiCnm x (k ^ 2)))
      (Real.jacobiSnm x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hd := Real.jacobiDnm_pos hm x
  have hpos : 0 < Real.jacobiDnm x (k ^ 2) - k * Real.jacobiCnm x (k ^ 2) := by
    nlinarith [sq_nonneg (Real.jacobiDnm x (k ^ 2) + k * Real.jacobiCnm x (k ^ 2))]
  refine ((((Real.hasDerivAt_jacobiDnm hm x).sub ((Real.hasDerivAt_jacobiCnm hm x).const_mul k)).log
    hpos.ne').const_mul k⁻¹).congr_deriv ?_
  try simp only [Pi.sub_apply]
  field_simp
  ring

/-- DLMF 22.14.2: `∫ cn(x,k) dx = k⁻¹ Arccos(dn(x,k))`, with the principal `arccos`, on
`0 < x < 2K` (where `sn x > 0`). -/
@[dlmf 22.14.E2 "special case: real x, 0 < k < 1, principal arccos on 0 < x < 2K"]
theorem Real.hasDerivAt_primitive_jacobiCn (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 2 * Real.compEllIntKm (k ^ 2)) :
    HasDerivAt (fun x => k⁻¹ * Real.arccos (Real.jacobiDnm x (k ^ 2)))
      (Real.jacobiCnm x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hd := Real.jacobiDnm_pos hm x
  have hs := je22b_jacobiSnm_pos hm hx0 hx1
  have hsq : √(1 - Real.jacobiDnm x (k ^ 2) ^ 2) = k * Real.jacobiSnm x (k ^ 2) := by
    rw [show 1 - Real.jacobiDnm x (k ^ 2) ^ 2 = (k * Real.jacobiSnm x (k ^ 2)) ^ 2 by
      linear_combination -h2]
    exact Real.sqrt_sq (by positivity)
  have hd1 : Real.jacobiDnm x (k ^ 2) ≠ 1 := by
    intro h; rw [h] at hsq; simp at hsq; rcases hsq with h | h <;> linarith
  have hdm1 : Real.jacobiDnm x (k ^ 2) ≠ -1 := by linarith
  refine (((Real.hasDerivAt_arccos hdm1 hd1).comp x (Real.hasDerivAt_jacobiDnm hm x)).const_mul
    k⁻¹).congr_deriv ?_
  rw [hsq]
  field_simp

/-- DLMF 22.14.3: `∫ dn(x,k) dx = Arcsin(sn(x,k))` with the principal `arcsin`
on `-K < x < K`. -/
@[dlmf 22.14.E3 "special case: real x, real parameter m = k² < 1, principal arcsin on |x| < K"]
theorem Real.hasDerivAt_arcsin_jacobiSnm {m : ℝ} (hm : m < 1) {x : ℝ}
    (hx0 : -Real.compEllIntKm m < x) (hx1 : x < Real.compEllIntKm m) :
    HasDerivAt (fun x => Real.arcsin (Real.jacobiSnm x m)) (Real.jacobiDnm x m) x := by
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hc := je22b_jacobiCnm_pos hm hx0 hx1
  have hsq : √(1 - Real.jacobiSnm x m ^ 2) = Real.jacobiCnm x m := by
    rw [show 1 - Real.jacobiSnm x m ^ 2 = Real.jacobiCnm x m ^ 2 by linear_combination -h1]
    exact Real.sqrt_sq hc.le
  have hs1 : Real.jacobiSnm x m ≠ 1 := by
    intro h; rw [h] at h1; nlinarith
  have hsm1 : Real.jacobiSnm x m ≠ -1 := by
    intro h; rw [h] at h1; nlinarith
  refine ((Real.hasDerivAt_arcsin hsm1 hs1).comp x (Real.hasDerivAt_jacobiSnm hm x)).congr_deriv ?_
  rw [hsq]
  field_simp

/-- DLMF 22.14.4: `∫ cd(x,k) dx = k⁻¹ ln(nd(x,k) + k sd(x,k))`, for all real `x`,
`0 < k < 1`. -/
@[dlmf 22.14.E4 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiCd (hk0 : 0 < k) (hk1 : k < 1) (x : ℝ) :
    HasDerivAt (fun x => k⁻¹ * Real.log (1 / Real.jacobiDnm x (k ^ 2) +
        k * (Real.jacobiSnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2))))
      (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hd := Real.jacobiDnm_pos hm x
  have hs := (je22b_abs_le_one (m := k ^ 2) x).1
  have hpos : 0 < 1 + k * Real.jacobiSnm x (k ^ 2) := by
    have := neg_abs_le (Real.jacobiSnm x (k ^ 2)); nlinarith
  have hpos' : 0 < 1 / Real.jacobiDnm x (k ^ 2) +
      k * (Real.jacobiSnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) := by
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
        Real.arcsin (-(k * (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)))))
      (Real.jacobiSnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hd := Real.jacobiDnm_pos hm x
  have hkp : 0 < √(1 - k ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hkp2 : √(1 - k ^ 2) ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by linarith)
  have hsq : √(1 - (-(k * (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)))) ^ 2) =
      √(1 - k ^ 2) / Real.jacobiDnm x (k ^ 2) := by
    rw [show 1 - (-(k * (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)))) ^ 2 =
        (√(1 - k ^ 2) / Real.jacobiDnm x (k ^ 2)) ^ 2 by
      field_simp; linear_combination (-k^2) * h1 + (1) * h2 + (-1) * hkp2]
    exact Real.sqrt_sq (by positivity)
  have hlt : (k * (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2))) ^ 2 < 1 := by
    have : (k * (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2))) ^ 2 =
        1 - (√(1 - k ^ 2) / Real.jacobiDnm x (k ^ 2)) ^ 2 := by
      field_simp; linear_combination (k^2) * h1 + (-1) * h2 + (1) * hkp2
    rw [this]; have : 0 < (√(1 - k ^ 2) / Real.jacobiDnm x (k ^ 2)) ^ 2 := by positivity
    linarith
  have hne1 : -(k * (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2))) ≠ 1 := by
    intro h; rw [← neg_sq, h] at hlt; norm_num at hlt
  have hnem1 : -(k * (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2))) ≠ -1 := by
    intro h; rw [← neg_sq, h] at hlt; norm_num at hlt
  refine (((Real.hasDerivAt_arcsin hnem1 hne1).comp x
    (((Real.hasDerivAt_jacobiCdm hm x).const_mul k).neg)).const_mul
      (k * √(1 - k ^ 2))⁻¹).congr_deriv ?_
  rw [hsq]
  field_simp
  linear_combination (0) * h1 + (0) * h2 + (-(Real.jacobiSnm x (k ^ 2))) * hkp2

/-- DLMF 22.14.6: `∫ nd(x,k) dx = k'⁻¹ Arccos(cd(x,k))`, principal `arccos`, on `0 < x < 2K`. -/
@[dlmf 22.14.E6 "special case: real x, 0 < k < 1, principal arccos on 0 < x < 2K"]
theorem Real.hasDerivAt_primitive_jacobiNd (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 2 * Real.compEllIntKm (k ^ 2)) :
    HasDerivAt (fun x => (√(1 - k ^ 2))⁻¹ *
        Real.arccos (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)))
      (1 / Real.jacobiDnm x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hd := Real.jacobiDnm_pos hm x
  have hs := je22b_jacobiSnm_pos hm hx0 hx1
  have hkp : 0 < √(1 - k ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hkp2 : √(1 - k ^ 2) ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by linarith)
  have hsq : √(1 - (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) ^ 2) =
      √(1 - k ^ 2) * Real.jacobiSnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2) := by
    rw [show 1 - (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) ^ 2 =
        (√(1 - k ^ 2) * Real.jacobiSnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) ^ 2 by
      field_simp; linear_combination (-k^2 - √(1 - k ^ 2)^2) * h1 + (1) * h2 +
          ((Real.jacobiCnm x (k ^ 2))^2 - 1) * hkp2]
    exact Real.sqrt_sq (by positivity)
  have hlt : (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) ^ 2 < 1 := by
    have : (Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) ^ 2 =
        1 - (√(1 - k ^ 2) * Real.jacobiSnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) ^ 2 := by
      field_simp; linear_combination (k^2 + √(1 - k ^ 2)^2) * h1 + (-1) * h2 + (1 -
          (Real.jacobiCnm x (k ^ 2))^2) * hkp2
    rw [this]
    have : 0 < (√(1 - k ^ 2) * Real.jacobiSnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2)) ^ 2 := by
      positivity
    linarith
  have hne1 : Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2) ≠ 1 := by
    intro h; rw [h] at hlt; norm_num at hlt
  have hnem1 : Real.jacobiCnm x (k ^ 2) / Real.jacobiDnm x (k ^ 2) ≠ -1 := by
    intro h; rw [h] at hlt; norm_num at hlt
  refine (((Real.hasDerivAt_arccos hnem1 hne1).comp x (Real.hasDerivAt_jacobiCdm hm x)).const_mul
    (√(1 - k ^ 2))⁻¹).congr_deriv ?_
  rw [hsq]
  field_simp
  linear_combination (0) * h1 + (0) * h2 + (-1) * hkp2

/-- DLMF 22.14.7: `∫ dc(x,k) dx = ln(nc(x,k) + sc(x,k))` for `-K < x < K`. -/
@[dlmf 22.14.E7 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiDc (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.compEllIntKm (k ^ 2) < x) (hx1 : x < Real.compEllIntKm (k ^ 2)) :
    HasDerivAt (fun x => Real.log (1 / Real.jacobiCnm x (k ^ 2) +
        Real.jacobiSnm x (k ^ 2) / Real.jacobiCnm x (k ^ 2)))
      (Real.jacobiDnm x (k ^ 2) / Real.jacobiCnm x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hc := je22b_jacobiCnm_pos hm hx0 hx1
  have hs : 0 < 1 + Real.jacobiSnm x (k ^ 2) := by
    nlinarith [sq_nonneg (1 + Real.jacobiSnm x (k ^ 2))]
  have hpos : 0 < 1 / Real.jacobiCnm x (k ^ 2) +
      Real.jacobiSnm x (k ^ 2) / Real.jacobiCnm x (k ^ 2) := by
    rw [← add_div]; positivity
  refine (((Real.hasDerivAt_jacobiNcm hm hc.ne').add (Real.hasDerivAt_jacobiScm hm hc.ne')).log
    hpos.ne').congr_deriv ?_
  try simp only [Pi.add_apply]
  field_simp
  linear_combination 0 * h1

/-- DLMF 22.14.8: `∫ nc(x,k) dx = k'⁻¹ ln(dc(x,k) + k' sc(x,k))` for `-K < x < K`. -/
@[dlmf 22.14.E8 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiNc (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.compEllIntKm (k ^ 2) < x) (hx1 : x < Real.compEllIntKm (k ^ 2)) :
    HasDerivAt (fun x => (√(1 - k ^ 2))⁻¹ * Real.log (Real.jacobiDnm x (k ^ 2) /
        Real.jacobiCnm x (k ^ 2) + √(1 - k ^ 2) * (Real.jacobiSnm x (k ^ 2) /
          Real.jacobiCnm x (k ^ 2))))
      (1 / Real.jacobiCnm x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hc := je22b_jacobiCnm_pos hm hx0 hx1
  have hd := Real.jacobiDnm_pos hm x
  have hkp : 0 < √(1 - k ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hkp2 : √(1 - k ^ 2) ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by linarith)
  have hnum : 0 < Real.jacobiDnm x (k ^ 2) + √(1 - k ^ 2) * Real.jacobiSnm x (k ^ 2) := by
    have hsq : (Real.jacobiDnm x (k ^ 2) - √(1 - k ^ 2) * Real.jacobiSnm x (k ^ 2)) *
        (Real.jacobiDnm x (k ^ 2) + √(1 - k ^ 2) * Real.jacobiSnm x (k ^ 2)) =
          Real.jacobiCnm x (k ^ 2) ^ 2 := by
      linear_combination (-k^2 - √(1 - k ^ 2)^2) * h1 + (1) * h2 + ((Real.jacobiCnm x (k ^ 2))^2 -
          1) * hkp2
    nlinarith [sq_pos_of_pos hc]
  have hpos : 0 < Real.jacobiDnm x (k ^ 2) / Real.jacobiCnm x (k ^ 2) +
      √(1 - k ^ 2) * (Real.jacobiSnm x (k ^ 2) / Real.jacobiCnm x (k ^ 2)) := by
    rw [mul_div_assoc', ← add_div]; positivity
  refine ((((Real.hasDerivAt_jacobiDcm hm hc.ne').add
    ((Real.hasDerivAt_jacobiScm hm hc.ne').const_mul
    √(1 - k ^ 2))).log hpos.ne').const_mul (√(1 - k ^ 2))⁻¹).congr_deriv ?_
  try simp only [Pi.add_apply]
  field_simp
  linear_combination (0) * h1 + (0) * h2 + (-(Real.jacobiSnm x (k ^ 2))) * hkp2

/-- DLMF 22.14.9: `∫ sc(x,k) dx = k'⁻¹ ln(dc(x,k) + k' nc(x,k))` for `-K < x < K`. -/
@[dlmf 22.14.E9 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiSc (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : -Real.compEllIntKm (k ^ 2) < x) (hx1 : x < Real.compEllIntKm (k ^ 2)) :
    HasDerivAt (fun x => (√(1 - k ^ 2))⁻¹ * Real.log (Real.jacobiDnm x (k ^ 2) /
        Real.jacobiCnm x (k ^ 2) + √(1 - k ^ 2) * (1 / Real.jacobiCnm x (k ^ 2))))
      (Real.jacobiSnm x (k ^ 2) / Real.jacobiCnm x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hc := je22b_jacobiCnm_pos hm hx0 hx1
  have hd := Real.jacobiDnm_pos hm x
  have hkp : 0 < √(1 - k ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hkp2 : √(1 - k ^ 2) ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by linarith)
  have hpos : 0 < Real.jacobiDnm x (k ^ 2) / Real.jacobiCnm x (k ^ 2) +
      √(1 - k ^ 2) * (1 / Real.jacobiCnm x (k ^ 2)) := by positivity
  refine ((((Real.hasDerivAt_jacobiDcm hm hc.ne').add
    ((Real.hasDerivAt_jacobiNcm hm hc.ne').const_mul
    √(1 - k ^ 2))).log hpos.ne').const_mul (√(1 - k ^ 2))⁻¹).congr_deriv ?_
  have hn : Real.jacobiDnm x (k ^ 2) + √(1 - k ^ 2) ≠ 0 := by positivity
  try simp only [Pi.add_apply]
  field_simp
  linear_combination (0) * h1 + (0) * h2 + (-(Real.jacobiSnm x (k ^ 2))) * hkp2

/-- DLMF 22.14.10: `∫ ns(x,k) dx = ln(ds(x,k) - cs(x,k))` for `0 < x < 2K`. -/
@[dlmf 22.14.E10 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiNs (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 2 * Real.compEllIntKm (k ^ 2)) :
    HasDerivAt (fun x => Real.log (Real.jacobiDnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2) -
        Real.jacobiCnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2)))
      (1 / Real.jacobiSnm x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hs := je22b_jacobiSnm_pos hm hx0 hx1
  have hd := Real.jacobiDnm_pos hm x
  have hdc : 0 < Real.jacobiDnm x (k ^ 2) - Real.jacobiCnm x (k ^ 2) := by
    have hsq : (Real.jacobiDnm x (k ^ 2) - Real.jacobiCnm x (k ^ 2)) *
        (Real.jacobiDnm x (k ^ 2) + Real.jacobiCnm x (k ^ 2)) =
          (1 - k ^ 2) * Real.jacobiSnm x (k ^ 2) ^ 2 := by linear_combination h2 - h1
    have : 0 < (1 - k ^ 2) * Real.jacobiSnm x (k ^ 2) ^ 2 := by
      have : 0 < 1 - k ^ 2 := by linarith
      positivity
    nlinarith
  have hpos : 0 < Real.jacobiDnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2) -
      Real.jacobiCnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2) := by
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
    (hx1 : x < 2 * Real.compEllIntKm (k ^ 2)) :
    HasDerivAt (fun x => Real.log (1 / Real.jacobiSnm x (k ^ 2) -
        Real.jacobiCnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2)))
      (Real.jacobiDnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hs := je22b_jacobiSnm_pos hm hx0 hx1
  have hc1 : 0 < 1 - Real.jacobiCnm x (k ^ 2) := by nlinarith [sq_pos_of_pos hs]
  have hpos : 0 < 1 / Real.jacobiSnm x (k ^ 2) -
      Real.jacobiCnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2) := by
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
    (hx1 : x < 2 * Real.compEllIntKm (k ^ 2)) :
    HasDerivAt (fun x => Real.log (1 / Real.jacobiSnm x (k ^ 2) -
        Real.jacobiDnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2)))
      (Real.jacobiCnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hs := je22b_jacobiSnm_pos hm hx0 hx1
  have hd := Real.jacobiDnm_pos hm x
  have hd1 : 0 < 1 - Real.jacobiDnm x (k ^ 2) := by
    have : 0 < k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2 := by positivity
    nlinarith
  have hpos : 0 < 1 / Real.jacobiSnm x (k ^ 2) -
      Real.jacobiDnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2) := by
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
    (hx0 : 0 < x) (hx1 : x < 2 * Real.compEllIntKm (k ^ 2)) :
    HasDerivAt (fun x => Real.log (Real.jacobiSnm x (k ^ 2) /
        (Real.jacobiCnm x (k ^ 2) + Real.jacobiDnm x (k ^ 2))))
      (1 / Real.jacobiSnm x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hs := je22b_jacobiSnm_pos hm hx0 hx1
  have hd := Real.jacobiDnm_pos hm x
  have hcd : 0 < Real.jacobiCnm x (k ^ 2) + Real.jacobiDnm x (k ^ 2) := by
    have hsq : (Real.jacobiDnm x (k ^ 2) - Real.jacobiCnm x (k ^ 2)) *
        (Real.jacobiDnm x (k ^ 2) + Real.jacobiCnm x (k ^ 2)) =
          (1 - k ^ 2) * Real.jacobiSnm x (k ^ 2) ^ 2 := by linear_combination h2 - h1
    have : 0 < (1 - k ^ 2) * Real.jacobiSnm x (k ^ 2) ^ 2 := by
      have : 0 < 1 - k ^ 2 := by linarith
      positivity
    nlinarith
  have hpos : 0 < Real.jacobiSnm x (k ^ 2) /
      (Real.jacobiCnm x (k ^ 2) + Real.jacobiDnm x (k ^ 2)) := by positivity
  refine (((Real.hasDerivAt_jacobiSnm hm x).div ((Real.hasDerivAt_jacobiCnm hm x).add
    (Real.hasDerivAt_jacobiDnm hm x)) hcd.ne').log hpos.ne').congr_deriv ?_
  try simp only [Pi.add_apply, Pi.div_apply]
  field_simp
  linear_combination ((Real.jacobiDnm x (k ^ 2))) * h1 + ((Real.jacobiCnm x (k ^ 2))) * h2

/-- DLMF 22.14.14: `∫ cn(x,k)/sn(x,k) dx = ½ ln((1 - dn(x,k))/(1 + dn(x,k)))` for
`0 < x < 2K`. -/
@[dlmf 22.14.E14 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiCn_div_jacobiSn (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 2 * Real.compEllIntKm (k ^ 2)) :
    HasDerivAt (fun x => 1 / 2 * Real.log ((1 - Real.jacobiDnm x (k ^ 2)) /
        (1 + Real.jacobiDnm x (k ^ 2))))
      (Real.jacobiCnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2)) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hs := je22b_jacobiSnm_pos hm hx0 hx1
  have hd := Real.jacobiDnm_pos hm x
  have hd1 : 0 < 1 - Real.jacobiDnm x (k ^ 2) := by
    have : 0 < k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2 := by positivity
    nlinarith
  have hpos : 0 < (1 - Real.jacobiDnm x (k ^ 2)) / (1 + Real.jacobiDnm x (k ^ 2)) := by
    positivity
  refine (((((Real.hasDerivAt_jacobiDnm hm x).const_sub 1).div
    ((Real.hasDerivAt_jacobiDnm hm x).const_add 1) (by positivity)).log hpos.ne').const_mul
      (1 / 2)).congr_deriv ?_
  have hd1' := hd1.ne'
  try simp only [Pi.div_apply]
  field_simp
  linear_combination (0) * h1 + (2*(Real.jacobiCnm x (k ^ 2))) * h2

/-- DLMF 22.14.15: `∫ cn(x,k)/sn²(x,k) dx = -dn(x,k)/sn(x,k)` for `0 < x < 2K`. -/
@[dlmf 22.14.E15 "special case: real x, 0 < k < 1"]
theorem Real.hasDerivAt_primitive_jacobiCn_div_jacobiSn_sq (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 2 * Real.compEllIntKm (k ^ 2)) :
    HasDerivAt (fun x => -(Real.jacobiDnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2)))
      (Real.jacobiCnm x (k ^ 2) / Real.jacobiSnm x (k ^ 2) ^ 2) x := by
  have hm : k ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2⟩ := je22b_identities hm x
  have hs := je22b_jacobiSnm_pos hm hx0 hx1
  refine (((Real.hasDerivAt_jacobiDnm hm x).div (Real.hasDerivAt_jacobiSnm hm x) hs.ne').neg
    ).congr_deriv ?_
  field_simp
  linear_combination (0) * h1 + ((Real.jacobiCnm x (k ^ 2))) * h2

end Other

/-! ### §22.14(iv): definite integrals -/

section Definite

variable {k : ℝ}

/-- DLMF 22.14.16: `∫₀^K ln sn(t,k) dt = -π K'(k)/4 - K(k) ln(k)/2`, `0 < k < 1`, with
`K = K(k²)`, `K' = K(1 - k²)` in the parameter convention. Admitted. -/
@[dlmf 22.14.E16 "special case: 0 < k < 1"]
theorem Real.integral_log_jacobiSnm (hk0 : 0 < k) (hk1 : k < 1) :
    ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.log (Real.jacobiSnm t (k ^ 2)) =
      -(π / 4) * Real.compEllIntKm (1 - k ^ 2) - 1 / 2 * Real.compEllIntKm (k ^ 2) * Real.log k :=
          by
  sorry

/-- DLMF 22.14.17: `∫₀^K ln cn(t,k) dt = -π K'(k)/4 + K(k) ln(k'/k)/2`, `0 < k < 1`.
Admitted. -/
@[dlmf 22.14.E17 "special case: 0 < k < 1"]
theorem Real.integral_log_jacobiCnm (hk0 : 0 < k) (hk1 : k < 1) :
    ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.log (Real.jacobiCnm t (k ^ 2)) =
      -(π / 4) * Real.compEllIntKm (1 - k ^ 2) +
        1 / 2 * Real.compEllIntKm (k ^ 2) * Real.log (√(1 - k ^ 2) / k) := by
  sorry

/-- DLMF 22.14.18: `∫₀^K ln dn(t,k) dt = K(k) ln(k')/2`, `0 < k < 1`. Admitted. -/
@[dlmf 22.14.E18 "special case: 0 < k < 1"]
theorem Real.integral_log_jacobiDnm (hk0 : 0 < k) (hk1 : k < 1) :
    ∫ t in (0 : ℝ)..Real.compEllIntKm (k ^ 2), Real.log (Real.jacobiDnm t (k ^ 2)) =
      1 / 2 * Real.compEllIntKm (k ^ 2) * Real.log (√(1 - k ^ 2)) := by
  sorry

end Definite

end DLMF.JacobiElliptic
