/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Asymptotics.ShiftedStirling
public import DLMFMathlib.Analysis.Asymptotics.WatsonGaussian

/-!
# Gamma-ratio normalization of quadratic-saddle expansions

The first-order shifted Gamma-ratio expansion transfers the first two terms of a
quadratic-saddle expansion through multiplication by `Γ(b)/Γ(b-a)`, with its remainder.
-/

@[expose] public noncomputable section

open Complex Filter Set Asymptotics
open scoped Topology

namespace DLMF.Gamma.GammaRatioNormalization

/-- Multiplication by `Γ(b)/Γ(b-a)` transfers a two-term quadratic-saddle expansion
to the corresponding positive-power expansion, for every fixed complex `a`. -/
theorem isBigO_mul_sub_two_term (a C0 C1 : ℂ) (J : ℝ → ℂ)
    (hJ : (fun b : ℝ => J b - (C0*(b:ℂ)^(-a/2)-C1*(b:ℂ)^(-(a+1)/2)))
      =O[atTop] (fun b : ℝ => (b:ℂ)^(-a/2-1))) :
    (fun b : ℝ => (Gamma (b:ℂ)/Gamma ((b:ℂ)-a))*J b -
      (C0*(b:ℂ)^(a/2)-C1*(b:ℂ)^((a-1)/2))) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(a/2-1)) := by
  let G : ℝ → ℂ := fun b => Gamma (b:ℂ) / Gamma ((b:ℂ)-a)
  have hG : G =O[atTop] (fun b : ℝ => (b:ℂ)^a) := by
    simpa [G, sub_eq_add_neg] using DLMF.Gamma.Gamma_ratio_expansion 0 (-a) 0
  have hD : (fun b : ℝ => G b - (b:ℂ)^a) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(a-1)) := by
    simpa [G, DLMF.Gamma.stirlingRatioG_zero, sub_eq_add_neg] using
      DLMF.Gamma.Gamma_ratio_expansion 0 (-a) 1
  have hproduct (u v : ℂ) : (fun b : ℝ => (b:ℂ)^u * (b:ℂ)^v) =ᶠ[atTop]
      (fun b : ℝ => (b:ℂ)^(u+v)) := by
    filter_upwards [eventually_gt_atTop 0] with b hb
    exact (cpow_add _ _ (ofReal_ne_zero.mpr hb.ne')).symm
  have hR := hG.mul hJ
  have hR' : (fun b : ℝ => G b * (J b - (C0*(b:ℂ)^(-a/2)-C1*(b:ℂ)^(-(a+1)/2))))
      =O[atTop] (fun b : ℝ => (b:ℂ)^(a/2-1)) := by
    refine hR.congr' EventuallyEq.rfl ?_
    filter_upwards [hproduct a (-a/2-1)] with b hb
    rw [hb]
    congr 1
    ring
  have h0 := (hD.mul (isBigO_refl (fun b : ℝ => (b:ℂ)^(-a/2)) atTop)).const_mul_left C0
  have h0' : (fun b : ℝ => (G b - (b:ℂ)^a) * (C0*(b:ℂ)^(-a/2))) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(a/2-1)) := by
    refine (h0.congr_left (fun b => by ring)).congr' EventuallyEq.rfl ?_
    filter_upwards [hproduct (a-1) (-a/2)] with b hb
    rw [hb]
    congr 1
    ring
  have h1 := (hD.mul (isBigO_refl (fun b : ℝ => (b:ℂ)^(-(a+1)/2)) atTop)).const_mul_left C1
  have h1' : (fun b : ℝ => (G b - (b:ℂ)^a) * (C1*(b:ℂ)^(-(a+1)/2))) =O[atTop]
      (fun b : ℝ => (b:ℂ)^(a/2-1)) := by
    have hh : (fun b : ℝ => (G b - (b:ℂ)^a) * (C1*(b:ℂ)^(-(a+1)/2))) =O[atTop]
        (fun b : ℝ => (b:ℂ)^(a/2-3/2)) := by
      refine (h1.congr_left (fun b => by ring)).congr' EventuallyEq.rfl ?_
      filter_upwards [hproduct (a-1) (-(a+1)/2)] with b hb
      rw [hb]
      congr 1
      ring
    refine hh.trans (isBigO_ofReal_cpow_of_re_le ?_)
    norm_num [sub_re, div_ofNat_re]
    linarith
  have h := hR'.add (h0'.sub h1')
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hb0 : (b:ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have he0 : (b:ℂ)^a * (b:ℂ)^(-a/2) = (b:ℂ)^(a/2) := by
    rw [← cpow_add _ _ hb0]
    congr 1
    ring
  have he1 : (b:ℂ)^a * (b:ℂ)^(-(a+1)/2) = (b:ℂ)^((a-1)/2) := by
    rw [← cpow_add _ _ hb0]
    congr 1
    ring
  dsimp only [G]
  linear_combination -C0*he0+C1*he1

end DLMF.Gamma.GammaRatioNormalization
