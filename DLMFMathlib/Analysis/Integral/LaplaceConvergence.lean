/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonRotated
public import Mathlib.Analysis.MellinTransform

/-!
# Absolute convergence and boundary continuity of Laplace transforms

An integrable power bound at zero reduces absolute Laplace convergence to local
integrability and convergence of the weighted tail. Absolute convergence on a boundary
line gives continuity on the closed half-plane and holomorphy in its interior.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology

/-- A Laplace transform is continuous on the closed half-plane of absolute convergence. -/
theorem continuousOn_integral_cexp_neg_mul_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {q : ℝ → E} {c : ℝ}
    (hq : IntegrableOn (fun t => Real.exp (-c * t) • q t) (Ioi 0)) :
    ContinuousOn (fun z : ℂ => ∫ t in Ioi (0 : ℝ), exp (-(z * t)) • q t)
      {z | c ≤ z.re} := by
  have hqm : AEStronglyMeasurable q (volume.restrict (Ioi 0)) := by
    have hm : AEStronglyMeasurable (fun t : ℝ => Real.exp (c * t))
        (volume.restrict (Ioi 0)) := (by fun_prop : Continuous _).aestronglyMeasurable
    refine (hm.smul hq.aestronglyMeasurable).congr (Eventually.of_forall fun t => ?_)
    change Real.exp (c * t) • (Real.exp (-c * t) • q t) = q t
    rw [smul_smul, ← Real.exp_add]
    simp
  apply continuousOn_of_dominated
    (bound := fun t : ℝ => Real.exp (-c * t) * ‖q t‖)
  · intro z _
    exact (by fun_prop : Continuous fun t : ℝ => exp (-(z * t))).aestronglyMeasurable.smul hqm
  · intro z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_smul, norm_exp]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    have hz' : c ≤ z.re := hz
    nlinarith [show 0 < t from ht]
  · exact hq.norm.congr (Eventually.of_forall fun t => by simp [norm_smul, Real.abs_exp])
  · filter_upwards [] with t
    exact (by fun_prop : Continuous fun z : ℂ => exp (-(z * t)) • q t).continuousOn

namespace MeasureTheory

/-- A locally integrable function with an integrable power bound at zero is integrable on
`(0,1]`. No condition at infinity is required. -/
theorem integrableOn_Ioc_of_isBigO_rpow {q : ℝ → ℂ} {s : ℝ} (hs : -1 < s)
    (hqi : LocallyIntegrableOn q (Ioi 0)) (hzero : q =O[𝓝[>] 0] fun t => t ^ s) :
    IntegrableOn q (Ioc 0 1) := by
  let g := (Iic (1 : ℝ)).indicator q
  have hgi : LocallyIntegrableOn g (Ioi 0) := by
    intro t ht
    obtain ⟨U, hU, hi⟩ := hqi t ht
    exact ⟨U, hU, hi.indicator measurableSet_Iic⟩
  have htop : g =O[atTop] (fun t : ℝ => t ^ (-2 : ℝ)) := by
    refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [g, not_le.mpr ht]
  have hbot : g =O[𝓝[>] 0] (fun t : ℝ => t ^ s) := by
    refine hzero.congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    simp [g, ht.2.le]
  have hi := mellinConvergent_of_isBigO_rpow (s := (1 : ℂ)) (a := 2) (b := -s)
    hgi htop (by norm_num) (by simpa using hbot) (by simp; linarith)
  simp only [MellinConvergent, sub_self, cpow_zero, one_smul] at hi
  have he : IntegrableOn g (Ioi 0) ↔ IntegrableOn q (Ioc 0 1) := by
    dsimp only [g]
    rw [integrableOn_indicator_iff measurableSet_Iic.nullMeasurableSet]
    rw [show Iic (1 : ℝ) ∩ Ioi 0 = Ioc 0 1 by ext t; simp [and_comm]]
  exact he.mp hi

/-- Given an integrable power bound at zero, absolute Laplace convergence is equivalent to
local integrability together with convergence of the weighted tail. -/
theorem integrableOn_exp_neg_smul_iff {q : ℝ → ℂ} {s σ : ℝ} (hs : -1 < s)
    (hzero : q =O[𝓝[>] 0] fun t => t ^ s) :
    IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 0) ↔
      LocallyIntegrableOn q (Ioi 0) ∧
        IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 1) := by
  constructor
  · intro hi
    refine ⟨?_, hi.mono_set (Ioi_subset_Ioi zero_le_one)⟩
    have hloc := hi.locallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed
      (by fun_prop : ContinuousOn (fun t : ℝ => Real.exp (σ * t)) (Ioi 0))
    convert hloc using 1
    funext t
    rw [smul_smul, ← Real.exp_add]
    simp
  · rintro ⟨hloc, htail⟩
    have hlo := integrableOn_Ioc_of_isBigO_rpow hs hloc hzero
    have hwlo := hlo.continuousOn_smul_of_subset
      (by fun_prop : ContinuousOn (fun t : ℝ => Real.exp (-σ * t)) (Icc 0 1))
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
    exact ⟨hwlo, htail⟩

end MeasureTheory
