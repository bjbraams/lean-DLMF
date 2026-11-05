/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.SpecialCases
public import DLMF.EllipticIntegrals.SymmetricConnection

/-!
# Limits of the symmetric third elliptic integral

Continuity at nonsingular parameters follows from Carlson's analytic continuation.
The change of parameter reduces the logarithmic divergence at zero to that of `R_C`.

## Main results

* `tendsto_symmetricEllipticRJ_zero`: logarithmic divergence at `p → 0±` for positive nodes
  (DLMF 19.20.7).
* `tendsto_symmetricEllipticRJ_zero_left`: the distinct limits at `p → 0+` and `p → 0-` when
  the first node vanishes (DLMF 19.20.10).
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals


namespace SymmetricParameterLimit

/-- The logarithmic divergence at zero, using a node at least as large as the second node. -/
theorem tendsto_symmetricEllipticRJ_zero_of_le {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : y ≤ x) :
    Tendsto (fun p : ℝ => (symmetricEllipticRJ x y z p).re) (𝓝[≠] 0) atTop := by
  let d : ℝ := (y - x) * (z - x)
  let q : ℝ → ℝ := fun p => x + d / (p - x)
  let q0 : ℝ := x - d / x
  let η : ℝ → ℝ := fun p => p * q p / x
  have hq0 : 0 < q0 := by
    have H : q0 = (x * y + (x - y) * z) / x := by dsimp [q0, d]; field_simp; ring
    rw [H]
    exact div_pos (add_pos_of_pos_of_nonneg (mul_pos hx hy)
      (mul_nonneg (sub_nonneg.mpr hxy) hz.le)) hx
  have hcont : ContinuousAt q 0 := by
    dsimp [q]
    fun_prop (disch := linarith)
  have hq : Tendsto q (𝓝[≠] 0) (𝓝 q0) := by
    have H : Tendsto q (𝓝[≠] 0) (𝓝 (q 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [q, zero_sub, div_neg_eq_neg_div, ← sub_eq_add_neg] using H
  have hqp : ∀ᶠ p : ℝ in 𝓝[≠] 0, 0 < q p := hq.eventually (eventually_gt_nhds hq0)
  have hp0 : ∀ᶠ p : ℝ in 𝓝[≠] 0, p ≠ 0 := self_mem_nhdsWithin
  have hpx : ∀ᶠ p : ℝ in 𝓝[≠] 0, p - x ≠ 0 := by
    filter_upwards [(eventually_ne_nhds (show (0 : ℝ) ≠ x by linarith)).filter_mono
      nhdsWithin_le_nhds] with p hp
    exact sub_ne_zero.mpr hp
  have hi : Tendsto (fun p : ℝ => p) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hη : Tendsto η (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [zero_mul, zero_div] using (hi.mul hq).div_const x
    · filter_upwards [hp0, hqp] with p hp hqp
      exact div_ne_zero (mul_ne_zero hp hqp.ne') hx.ne'
  have hRC := (tendsto_symmetricEllipticRC_zero (div_pos (mul_pos hy hz) hx)).comp hη
  have hJ := (continuousAt_symmetricEllipticRJ_parameter
    (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
    (ofReal_mem_slitPlane.mpr hz) (ofReal_mem_slitPlane.mpr hq0)).tendsto.comp
      ((continuous_ofReal.tendsto q0).comp hq)
  have hJr := (continuous_re.tendsto _).comp hJ
  have hfinite : Tendsto (fun p : ℝ => 3 * (symmetricEllipticRF x y z).re -
      (q p - x) * (symmetricEllipticRJ x y z (q p)).re) (𝓝[≠] 0)
      (𝓝 (3 * (symmetricEllipticRF x y z).re -
        (q0 - x) * (symmetricEllipticRJ x y z q0).re)) :=
    tendsto_const_nhds.sub ((hq.sub tendsto_const_nhds).mul hJr)
  have hNeg := hfinite.add_atBot
    (tendsto_neg_atTop_atBot.comp (hRC.const_mul_atTop (by norm_num : (0 : ℝ) < 3)))
  have hInv : Tendsto (fun p : ℝ => (p - x)⁻¹) (𝓝[≠] 0) (𝓝 (-x)⁻¹) := by
    simpa only [zero_sub] using
      (hi.sub (tendsto_const_nhds (x := x))).inv₀ (by simpa using hx.ne')
  have H := hNeg.atBot_mul_neg
    (by simpa only [inv_neg] using neg_neg_of_pos (inv_pos.mpr hx)) hInv
  apply H.congr'
  filter_upwards [hp0, hqp, hpx] with p hp hqp hpx
  have hrel : (p - x) * (q p - x) = (y - x) * (z - x) := by
    dsimp [q, d]
    field_simp
    ring
  have hchange := symmetricEllipticRJ_change_parameter' hx hy.le hz.le
    (fun _ => hz.ne') hp hqp.ne' hrel
  have hre := congrArg Complex.re hchange
  norm_num [mul_re] at hre
  change (3 * (symmetricEllipticRF x y z).re -
    (q p - x) * (symmetricEllipticRJ x y z (q p)).re +
      -(3 * (symmetricEllipticRC (y * z / x : ℝ) (η p)).re)) * (p - x)⁻¹ = _
  have hm : 3 * (symmetricEllipticRF x y z).re -
      (q p - x) * (symmetricEllipticRJ x y z (q p)).re +
        -(3 * (symmetricEllipticRC (y * z / x : ℝ) (η p)).re) =
      (p - x) * (symmetricEllipticRJ x y z p).re := by
    dsimp only [η]
    push_cast
    linear_combination -hre
  rw [hm]
  field_simp

end SymmetricParameterLimit

/-- DLMF 19.20.7: `R_J(x, y, z, p) → +∞` as `p → 0±`, for `x, y, z > 0` (for `p < 0` the
principal value). -/
@[dlmf 19.20.E7]
theorem tendsto_symmetricEllipticRJ_zero {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Tendsto (fun p : ℝ => (symmetricEllipticRJ x y z p).re) (𝓝[≠] 0) atTop := by
  rcases le_total y x with hxy | hxy
  · exact SymmetricParameterLimit.tendsto_symmetricEllipticRJ_zero_of_le hx hy hz hxy
  · simpa only [symmetricEllipticRJ_comm_left] using
      SymmetricParameterLimit.tendsto_symmetricEllipticRJ_zero_of_le hy hx hz hxy

/-- DLMF 19.20.10: `lim_{p→0+} √p R_J(0, y, z, p) = 3π/(2√y√z)` and
`lim_{p→0-} R_J(0, y, z, p) = -R_D(0, y, z) - R_D(0, z, y) = -6/(yz) R_G(0, y, z)`, for
`y, z > 0`. -/
@[dlmf 19.20.E10]
theorem tendsto_symmetricEllipticRJ_zero_left {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    Tendsto (fun p : ℝ => (Real.sqrt p : ℂ) * symmetricEllipticRJ 0 y z p) (𝓝[>] 0)
        (𝓝 (3 * π / (2 * Real.sqrt y * Real.sqrt z) : ℝ)) ∧
      Tendsto (fun p : ℝ => symmetricEllipticRJ 0 y z p) (𝓝[<] 0)
        (𝓝 (-symmetricEllipticRD 0 y z - symmetricEllipticRD 0 z y)) ∧
      -symmetricEllipticRD 0 y z - symmetricEllipticRD 0 z y = -6 / ((y : ℂ) * z) *
          symmetricEllipticRG 0 y z := by
  let q : ℝ → ℝ := fun p => z + z * (z - y) / (p - z)
  let η : ℝ → ℝ := fun p => p * q p / z
  let F : ℝ → ℂ := fun p => 3 * symmetricEllipticRF 0 y z -
    ((q p - z : ℝ) : ℂ) * symmetricEllipticRJ 0 y z (q p)
  have hq00 : q 0 = y := by dsimp [q]; field_simp [hz.ne']; ring
  have hq : Tendsto q (𝓝 0) (𝓝 y) := by
    have H : ContinuousAt q 0 := by dsimp [q]; fun_prop (disch := linarith)
    simpa only [hq00] using H.tendsto
  have hqp : ∀ᶠ p : ℝ in 𝓝 0, 0 < q p := hq.eventually (eventually_gt_nhds hy)
  have hpx : ∀ᶠ p : ℝ in 𝓝 0, p - z ≠ 0 := by
    filter_upwards [eventually_ne_nhds (show (0 : ℝ) ≠ z by linarith)] with p hp
    exact sub_ne_zero.mpr hp
  have hys := ofReal_mem_slitPlane.mpr hy
  have hzs := ofReal_mem_slitPlane.mpr hz
  have hJ := (continuousAt_symmetricEllipticRJ_zero_parameter hys hzs hys).tendsto.comp
    ((continuous_ofReal.tendsto y).comp hq)
  have hF : Tendsto F (𝓝 0) (𝓝 (3 * symmetricEllipticRF 0 y z -
      ((y - z : ℝ) : ℂ) * symmetricEllipticRJ 0 y z y)) :=
    tendsto_const_nhds.sub (((continuous_ofReal.tendsto (y - z)).comp
      (hq.sub tendsto_const_nhds)).mul hJ)
  have hDen : Tendsto (fun p : ℝ => ((p - z : ℝ) : ℂ)) (𝓝 0) (𝓝 (-z : ℂ)) := by
    have H : ContinuousAt (fun p : ℝ => ((p - z : ℝ) : ℂ)) 0 := by fun_prop
    simpa only [zero_sub, ofReal_neg] using H.tendsto
  have hden : (-z : ℂ) ≠ 0 := neg_ne_zero.mpr (ofReal_ne_zero.mpr hz.ne')
  have hchange (p : ℝ) (hp : p ≠ 0) (hqp : 0 < q p) (hpx : p - z ≠ 0) :
      ((p - z : ℝ) : ℂ) * symmetricEllipticRJ 0 y z p = F p - 3 * symmetricEllipticRC 0 (η p) := by
    have hrel : (p - z) * (q p - z) = (0 - z) * (y - z) := by
      dsimp [q]; field_simp; ring
    have H := symmetricEllipticRJ_change_parameter' hz (le_refl (0 : ℝ)) hy.le
      (fun _ => hy.ne') hp hqp.ne' hrel
    simp only [symmetricEllipticRJ_comm_left 0 z, symmetricEllipticRJ_comm_right 0 y z,
      symmetricEllipticRF_comm_left 0 z, symmetricEllipticRF_comm_right 0 y z,
      zero_mul, zero_div, ofReal_zero] at H
    dsimp only [F, η]
    linear_combination H
  have hS : Tendsto (fun p : ℝ => (Real.sqrt p : ℂ)) (𝓝 0) (𝓝 0) := by
    have H : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa only [Real.sqrt_zero] using Real.continuous_sqrt.tendsto (0 : ℝ)
    exact (continuous_ofReal.tendsto 0).comp H
  have hR : Tendsto (fun p : ℝ => (Real.sqrt (z / q p) : ℂ)) (𝓝 0)
      (𝓝 (Real.sqrt (z / y) : ℂ)) :=
    (continuous_ofReal.tendsto _).comp ((tendsto_const_nhds.div hq hy.ne').sqrt)
  have hLpos := ((hS.mul hF).sub (hR.const_mul (3 * (π : ℂ) / 2))).div hDen hden
  have hLposeq : (0 * (3 * symmetricEllipticRF 0 y z -
      ((y - z : ℝ) : ℂ) * symmetricEllipticRJ 0 y z y) -
      3 * (π : ℂ) / 2 * Real.sqrt (z / y)) / (-z : ℂ) =
      ((3 * π / (2 * Real.sqrt y * Real.sqrt z) : ℝ) : ℂ) := by
    rw [Real.sqrt_div hz.le]
    have hsy : (Real.sqrt y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
    have hsz : (Real.sqrt z : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hz).ne'
    have hsq : (Real.sqrt z : ℂ) ^ 2 = z := by exact_mod_cast Real.sq_sqrt hz.le
    push_cast
    field_simp [ofReal_ne_zero.mpr hz.ne']
    linear_combination (3 * (π : ℂ)) * hsq
  rw [hLposeq] at hLpos
  have hPos : Tendsto (fun p : ℝ => (Real.sqrt p : ℂ) * symmetricEllipticRJ 0 y z p)
      (𝓝[>] 0) (𝓝 ((3 * π / (2 * Real.sqrt y * Real.sqrt z) : ℝ) : ℂ)) := by
    apply (hLpos.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin, hqp.filter_mono nhdsWithin_le_nhds,
      hpx.filter_mono nhdsWithin_le_nhds] with p hp hqp hpx
    have hp0 : 0 < p := hp
    have hη : 0 < η p := div_pos (mul_pos hp0 hqp) hz
    have hrc := symmetricEllipticRC_special.2.2.1 (η p) (ofReal_mem_slitPlane.mpr hη)
    rw [cpow_neg, Carlson.ofReal_cpow_half hη.le] at hrc
    have hroot : Real.sqrt p / Real.sqrt (η p) = Real.sqrt (z / q p) := by
      dsimp only [η]
      rw [Real.sqrt_div (mul_pos hp0 hqp).le, Real.sqrt_mul hp0.le, Real.sqrt_div hz.le]
      field_simp [(Real.sqrt_pos.mpr hp0).ne', (Real.sqrt_pos.mpr hqp).ne',
        (Real.sqrt_pos.mpr hz).ne']
    have hscaled : (Real.sqrt p : ℂ) * symmetricEllipticRC 0 (η p) =
        (π : ℂ) / 2 * Real.sqrt (z / q p) := by
      rw [hrc]
      have hc : (Real.sqrt p : ℂ) / (Real.sqrt (η p) : ℂ) = Real.sqrt (z / q p) := by
        exact_mod_cast hroot
      linear_combination (π : ℂ) / 2 * hc
    symm
    apply (eq_div_iff (ofReal_ne_zero.mpr hpx)).mpr
    linear_combination (Real.sqrt p : ℂ) * hchange p hp0.ne' hqp hpx - 3 * hscaled
  have hNeg := hF.div hDen hden
  have hLnegeq : (3 * symmetricEllipticRF 0 y z -
      ((y - z : ℝ) : ℂ) * symmetricEllipticRJ 0 y z y) / (-z : ℂ) =
      -symmetricEllipticRD 0 y z - symmetricEllipticRD 0 z y := by
    have H := symmetricEllipticRF_zero_eq_symmetricEllipticRD hys hzs
    rw [symmetricEllipticRJ_comm_right]
    change (3 * symmetricEllipticRF 0 y z - ((y - z : ℝ) : ℂ) *
      symmetricEllipticRD 0 z y) / (-z : ℂ) = _
    apply (div_eq_iff hden).mpr
    push_cast
    linear_combination H
  rw [hLnegeq] at hNeg
  have hNeg' : Tendsto (fun p : ℝ => symmetricEllipticRJ 0 y z p) (𝓝[<] 0)
      (𝓝 (-symmetricEllipticRD 0 y z - symmetricEllipticRD 0 z y)) := by
    apply (hNeg.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin, hqp.filter_mono nhdsWithin_le_nhds,
      hpx.filter_mono nhdsWithin_le_nhds] with p hp hqp hpx
    have hp0 : p < 0 := hp
    have hη : η p < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hp0 hqp) hz
    have H := hchange p hp0.ne hqp hpx
    rw [symmetricEllipticRC_special.2.2.2 (η p) hη, mul_zero, sub_zero] at H
    symm
    apply (eq_div_iff (ofReal_ne_zero.mpr hpx)).mpr
    linear_combination H
  refine ⟨hPos, hNeg', ?_⟩
  have H := (symmetricEllipticRG_zero_eq hys hzs).1
  field_simp [ofReal_ne_zero.mpr hy.ne', ofReal_ne_zero.mpr hz.ne']
  linear_combination H

end DLMF.EllipticIntegrals
