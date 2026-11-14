/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Ring

/-!
# Integration of uniformly bounded weighted series

An absolutely summable family of coefficients may be integrated term by term against an
integrable weight when the remaining factors have norm at most one. Values lie in a
commutative real normed algebra; completeness is unnecessary for Mathlib's totalized integral.
The proof uses Mathlib's dominated convergence theorem for series and its integrable
constant-multiplication identity.

* `MeasureTheory.hasSum_integral_mul_of_norm_le_one`: termwise integration with a bounded factor.
-/

public noncomputable section
open MeasureTheory Filter
namespace MeasureTheory

/-- Termwise integration of a series with a bounded integrable weight. -/
lemma hasSum_integral_mul_of_norm_le_one {K α ι : Type*} [NormedCommRing K]
    [NormedAlgebra ℝ K] [MeasurableSpace α] [Countable ι]
    {μ : Measure α}
    {w : α → K} (hw : Integrable w μ) {d : ι → K} (hd : Summable fun i => ‖d i‖)
    {e : ι → α → K} (he : ∀ i, AEStronglyMeasurable (e i) μ) (hbd : ∀ i, ∀ᵐ t ∂μ, ‖e i t‖ ≤ 1)
    {g : α → K} (hg : ∀ᵐ t ∂μ, HasSum (fun i => d i * e i t) (g t)) :
    HasSum (fun i => d i * ∫ t, w t * e i t ∂μ) (∫ t, w t * g t ∂μ) := by
  have h := hasSum_integral_of_dominated_convergence (μ := μ)
    (F := fun i t => w t * (d i * e i t)) (f := fun t => w t * g t)
    (fun i t => ‖d i‖ * ‖w t‖)
    (fun i => hw.aestronglyMeasurable.mul (aestronglyMeasurable_const.mul (he i)))
    (fun i => by
      filter_upwards [hbd i] with t ht
      calc ‖w t * (d i * e i t)‖ ≤ ‖w t‖ * (‖d i‖ * ‖e i t‖) :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ ‖w t‖ * (‖d i‖ * 1) := by gcongr
        _ = _ := by ring)
    (Eventually.of_forall fun t => hd.mul_right _)
    (by simp_rw [tsum_mul_right]; exact hw.norm.const_mul _)
    (by filter_upwards [hg] with t ht using ht.mul_left (w t))
  refine h.congr_fun fun i => ?_
  have hwi : Integrable (fun t => w t * e i t) μ := by
    apply hw.norm.mono' (hw.aestronglyMeasurable.mul (he i))
    filter_upwards [hbd i] with t ht
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) ht)
  rw [← integral_const_mul_of_integrable hwi]
  congr 1
  funext t
  ring


end MeasureTheory
