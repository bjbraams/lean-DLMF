/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Mellin.Transforms
public import DLMF.Gamma.VerticalStrips
public import DLMFMathlib.Analysis.MellinBounds
public import Mathlib.Analysis.Meromorphic.Complex

/-!
# Vertical bounds for continued Mellin transforms

Subtracting finitely many terms of an asymptotic expansion gives a Mellin integral
convergent to the right of any fixed strip. The subtracted principal parts are bounded
at large height, so the continued high-tail transform is uniformly bounded there.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex
open scoped Topology Real

namespace DLMF.AsymptoticApproximations

/-- The nonoscillatory high-tail continuation is bounded at large height, uniformly to
the left of any fixed vertical line. -/
theorem exists_bound_mellin_truncHigh_continuation {h : ℝ → ℂ} {b β : ℕ → ℂ}
    {H : ℂ → ℂ} (hhc : LocallyIntegrableOn h (Ioi 0))
    (hβ : StrictMono fun s => (β s).re)
    (hβinf : Tendsto (fun s => (β s).re) atTop atTop)
    (hh : HasAsymptoticExpansion atTop (fun s (t : ℝ) => (t : ℂ) ^ (-β s)) b h)
    (hH : ∀ z : ℂ, z.re < (β 0).re → H z = mellin (mellinTruncHigh h) z)
    (hHd : ∀ N : ℕ, DifferentiableOn ℂ (fun z => H z + ∑ s ∈ range N, b s / (z - β s))
      {z : ℂ | z.re < (β N).re}) (L : ℝ) :
    ∃ B Y : ℝ, 0 ≤ B ∧ 1 ≤ Y ∧ ∀ z : ℂ, z.re ≤ L → Y ≤ |z.im| → ‖H z‖ ≤ B := by
  obtain ⟨N, hN⟩ := (hβinf.eventually_gt_atTop L).exists
  let g : ℝ → ℂ := mellinTruncHigh
    (fun t => h t - ∑ s ∈ range N, (t : ℂ) ^ (-β s) • b s)
  have hi : MellinConvergent g L := mellinConvergent_truncHigh_sub_sum hhc hh N
    (by simpa using hN)
  let M : ℝ := ∫ t in Ioi 0, t ^ (L - 1) * ‖g t‖
  have hM : 0 ≤ M := setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _)
  let Y : ℝ := 1 + ∑ s ∈ range N, |(β s).im|
  have hY : 1 ≤ Y := by
    have hs : 0 ≤ ∑ s ∈ range N, |(β s).im| := sum_nonneg fun s _ => abs_nonneg _
    dsimp [Y]
    linarith
  refine ⟨M + ∑ s ∈ range N, ‖b s‖, Y, by positivity, hY, fun z hz hzY => ?_⟩
  have hreg := mellin_truncHigh_continuation_regularPart_eq hhc hβ hh hH hHd N
    (lt_of_le_of_lt hz hN)
  change H z + ∑ s ∈ range N, b s / (z - β s) = mellin g z at hreg
  have hm : ‖mellin g z‖ ≤ M := norm_mellin_le_of_support_gt_one
    (fun t ht => by simp [g, mellinTruncHigh_eq_indicator, not_lt.mpr ht]) hi hz
  have hden (s : ℕ) (hs : s ∈ range N) : 1 ≤ ‖z - β s‖ := by
    have hsle : |(β s).im| ≤ ∑ k ∈ range N, |(β k).im| :=
      Finset.single_le_sum (fun k _ => abs_nonneg ((β k).im)) hs
    have him : 1 ≤ |z.im - (β s).im| := by
      have ht := abs_sub_abs_le_abs_sub z.im (β s).im
      dsimp [Y] at hzY
      linarith
    exact him.trans (by simpa using abs_im_le_norm (z - β s))
  have hsum : ‖∑ s ∈ range N, b s / (z - β s)‖ ≤ ∑ s ∈ range N, ‖b s‖ := by
    apply (norm_sum_le _ _).trans
    exact sum_le_sum fun s hs => by
      rw [norm_div]
      exact div_le_self (norm_nonneg _) (hden s hs)
  calc ‖H z‖ = ‖mellin g z - ∑ s ∈ range N, b s / (z - β s)‖ := by
        congr 1
        linear_combination hreg
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hm hsum)

/-- Holomorphic regular parts with exponents tending right give a meromorphic high-tail
continuation on the whole plane, including exceptional values at the poles. -/
theorem meromorphic_mellin_truncHigh_continuation {b β : ℕ → ℂ} {H : ℂ → ℂ}
    (hβinf : Tendsto (fun s => (β s).re) atTop atTop)
    (hHd : ∀ N : ℕ, DifferentiableOn ℂ (fun z => H z + ∑ s ∈ range N, b s / (z - β s))
      {z : ℂ | z.re < (β N).re}) : Meromorphic H := by
  intro z
  obtain ⟨N, hN⟩ := (hβinf.eventually_gt_atTop z.re).exists
  have ha := (hHd N).analyticOnNhd (isOpen_lt continuous_re continuous_const) z hN
  have hs : MeromorphicAt (fun w : ℂ => ∑ s ∈ range N, b s / (w - β s)) z :=
    MeromorphicAt.fun_sum fun s _ =>
      analyticAt_const.meromorphicAt.div
        ((analyticAt_id.sub analyticAt_const).meromorphicAt)
  convert ha.meromorphicAt.sub hs using 1
  funext w
  simp only [Pi.sub_apply]
  ring

/-- A finite-subtraction continuation is holomorphic away from its exponent locations. -/
theorem differentiableAt_mellin_truncHigh_continuation {b β : ℕ → ℂ} {H : ℂ → ℂ}
    (hβinf : Tendsto (fun s => (β s).re) atTop atTop)
    (hHd : ∀ N : ℕ, DifferentiableOn ℂ (fun z => H z + ∑ s ∈ range N, b s / (z - β s))
      {z : ℂ | z.re < (β N).re}) {z : ℂ} (hz : ∀ k, z ≠ β k) :
    DifferentiableAt ℂ H z := by
  obtain ⟨N, hN⟩ := (hβinf.eventually_gt_atTop z.re).exists
  have ha := (hHd N).differentiableAt
    ((isOpen_lt continuous_re continuous_const).mem_nhds hN)
  have hs : DifferentiableAt ℂ (fun w : ℂ => ∑ s ∈ range N, b s / (w - β s)) z :=
    DifferentiableAt.fun_sum fun k _ => (differentiableAt_const (b k)).div
      (differentiableAt_id.sub_const (β k)) (sub_ne_zero.mpr (hz k))
  convert ha.sub hs using 1
  funext w
  simp only [Pi.sub_apply]
  ring

end DLMF.AsymptoticApproximations
