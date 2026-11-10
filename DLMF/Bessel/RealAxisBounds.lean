/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Asymptotics
public import DLMF.Bessel.Lommel

/-!
# Bounds for Bessel J on the positive real axis

The large-argument cosine expansion bounds `J_ν(x)` by `O(x^(-1/2))` for every fixed
complex order. The imaginary part of its cosine phase is constant on the real axis.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics
open scoped Real Topology
namespace DLMF.Bessel
/-- For fixed complex order, Bessel J is `O(x^(-1/2))` as real `x → +∞`. -/
theorem isBigO_besselJ_atTop (ν : ℂ) :
    (fun x : ℝ => besselJ ν x) =O[atTop] (fun x : ℝ => x^(-(1/2):ℝ)) := by
  let c : ℂ := ν*π/2+π/4
  have hcos (x : ℝ) : ‖cos ((x:ℂ)-c)‖ ≤ ‖cos c‖+‖sin c‖ := by
    rw [Complex.cos_sub]
    calc ‖cos (x:ℂ)*cos c+sin (x:ℂ)*sin c‖ ≤
        ‖cos (x:ℂ)*cos c‖+‖sin (x:ℂ)*sin c‖ := norm_add_le _ _
      _ ≤ ‖cos c‖+‖sin c‖ := by
        simp only [norm_mul, ← ofReal_cos, ← ofReal_sin, norm_real, Real.norm_eq_abs]
        nlinarith [Real.abs_cos_le_one x, Real.abs_sin_le_one x,
          norm_nonneg (cos c), norm_nonneg (sin c)]
  have hmain : (fun x : ℝ => (Real.sqrt (2/(π*x)):ℂ)*cos ((x:ℂ)-c)) =O[atTop]
      (fun x : ℝ => x^(-(1/2):ℝ)) := by
    refine IsBigO.of_bound (Real.sqrt (2/π)*(‖cos c‖+‖sin c‖)) ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have hs : Real.sqrt (2/(π*x)) = Real.sqrt (2/π)*x^(-(1/2):ℝ) := by
      rw [show 2/(π*x) = (2/π)/x by ring, Real.sqrt_div (by positivity),
        Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.rpow_neg hx.le, div_eq_mul_inv]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), hs,
      Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
    calc _ ≤ (Real.sqrt (2/π)*x^(-(1/2):ℝ))*(‖cos c‖+‖sin c‖) :=
          mul_le_mul_of_nonneg_left (hcos x) (by positivity)
      _ = _ := by ring
  have herr : (fun x : ℝ => x^(-(3/2):ℝ)) =O[atTop] (fun x : ℝ => x^(-(1/2):ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hd : (fun x : ℝ => besselJ ν x -
      (Real.sqrt (2/(π*x)):ℂ)*cos ((x:ℂ)-c)) =O[atTop]
      (fun x : ℝ => x^(-(1/2):ℝ)) := by
    simpa only [c, sub_add_eq_sub_sub] using (besselJ_sub_cos_isBigO ν).trans herr
  simpa only [Pi.add_apply, sub_add_cancel] using hd.add hmain
/-- Bounds for `J_ν(ct)` by `t^(Re ν)` near zero and by `t^(-1/2)` near infinity. -/
theorem exists_norm_besselJ_mul_bounds (ν : ℂ) {c : ℝ} (hc : 0 < c) :
    ∃ T M K : ℝ, 0 < T ∧ 0 ≤ M ∧ 0 ≤ K ∧
      (∀ t ∈ Ioc (0:ℝ) T, ‖besselJ ν (c*t)‖ ≤ M*t^ν.re) ∧
      ∀ t ∈ Ioi T, ‖besselJ ν (c*t)‖ ≤ K*t^(-(1/2):ℝ) := by
  have hb := (isBigO_besselJ_atTop ν).comp_tendsto (tendsto_id.const_mul_atTop hc)
  obtain ⟨C,hC,hbound⟩ := hb.exists_pos
  obtain ⟨X,hX⟩ := eventually_atTop.mp hbound.bound
  let T : ℝ := max X 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨M,hM⟩ := exists_norm_besselJ_mul_le ν (mul_pos hc hT)
  refine ⟨T, max M 0*T^(-ν.re), C*c^(-(1/2):ℝ), hT, by positivity, by positivity, ?_, ?_⟩
  · intro t ht
    have ht0 : 0 < t := ht.1
    have hu : t/T ∈ Ioc (0:ℝ) 1 := ⟨div_pos ht0 hT, (div_le_one hT).mpr ht.2⟩
    have h := hM (t/T) hu
    rw [← ofReal_mul, show c*T*(t/T)=c*t by field_simp] at h
    rw [Real.div_rpow ht0.le hT.le, div_eq_mul_inv, ← Real.rpow_neg hT.le] at h
    calc ‖besselJ ν (c*t)‖ ≤ M*(t^ν.re*T^(-ν.re)) := by simpa only [ofReal_mul] using h
      _ ≤ max M 0*(t^ν.re*T^(-ν.re)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = _ := by ring
  · intro t ht
    have ht0 : 0 < t := hT.trans ht
    have h := hX t ((le_max_left _ _).trans ht.le)
    simp only [Function.comp_apply, id_eq, Real.norm_of_nonneg
      (Real.rpow_nonneg (mul_pos hc ht0).le _)] at h
    rw [Real.mul_rpow hc.le ht0.le] at h
    convert h using 1 <;> push_cast <;> ring
end DLMF.Bessel
