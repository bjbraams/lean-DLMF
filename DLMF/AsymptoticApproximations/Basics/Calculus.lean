/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Basics.OrderSymbols
public import DLMFMathlib.Analysis.Asymptotics.IntegralPowerSeries
public import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Termwise calculus of Poincaré expansions

Ritt's bound differentiates a holomorphic Poincaré expansion termwise in every closed
subsector strictly inside its open sector, as in DLMF §2.1(ii). Tail integration of inverse
power series is supplied by `Asymptotics.HasAsymptoticExpansion.integral_Ioi_inv_pow`.
-/

@[expose] public noncomputable section

open Complex Filter Set Asymptotics Finset Bornology
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- The inverse-power monomial has the usual derivative away from zero. -/
private theorem hasDerivAt_inv_pow {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    HasDerivAt (fun w : ℂ => w⁻¹ ^ n) (-(n : ℂ) * z⁻¹ ^ (n + 1)) z := by
  convert hasDerivAt_zpow (-(n : ℤ)) z (Or.inl hz) using 1
  · funext w
    simp only [zpow_neg, zpow_natCast, inv_pow]
  · rw [show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by omega]
    simp only [Int.cast_neg, Int.cast_natCast, zpow_neg, zpow_natCast, inv_pow]

/-- DLMF §2.1(ii): a holomorphic Poincaré expansion can be differentiated termwise in
every closed subsector strictly inside its open sector. -/
@[dlmf 2.1.ii]
theorem HasPoincareExpansion.deriv {f : ℂ → ℂ} {a : ℕ → ℂ} {θ ω ω' R : ℝ}
    (hf : HasPoincareExpansion (rittSector θ ω R) a f)
    (han : AnalyticOnNhd ℂ f (rittSector θ ω R)) (hω : ω ≤ Real.pi) (hωω' : ω' < ω) :
    HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 (rittClosedSector θ ω'))
      (fun n (z : ℂ) => z⁻¹ ^ (n + 1)) (fun n => -(n : ℂ) * a n) (deriv f) := by
  intro N
  let S := rittSector θ ω (max R 0)
  let P : ℂ → ℂ := fun z => ∑ n ∈ range N, z⁻¹ ^ n * a n
  have hsub : S ⊆ rittSector θ ω R := fun z hz =>
    ⟨(le_max_left R 0).trans_lt hz.1, hz.2⟩
  have hp (z : ℂ) (hz : z ≠ 0) : HasDerivAt P
      (∑ n ∈ range N, (-(n : ℂ) * z⁻¹ ^ (n + 1)) * a n) z :=
    HasDerivAt.fun_sum fun n _ => (hasDerivAt_inv_pow hz n).mul_const (a n)
  have hdiff : DifferentiableOn ℂ (fun z => f z - P z) S := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp ((le_max_right R 0).trans_lt hz.1)
    exact ((han z (hsub hz)).differentiableAt.sub
      (hp z hz0).differentiableAt).differentiableWithinAt
  have hrem : (fun z => f z - P z) =O[cobounded ℂ ⊓ 𝓟 S]
      (fun z : ℂ => z⁻¹ ^ N) := by
    simpa only [P, smul_eq_mul] using (hf N).mono
      (inf_le_inf_left _ (principal_mono.mpr hsub))
  have hcomp : (fun z : ℂ => z⁻¹ ^ N) =O[cobounded ℂ ⊓ 𝓟 S]
      (fun z : ℂ => ‖z‖ ^ (-(N : ℝ))) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
    rw [one_mul, norm_pow, norm_inv, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast,
      inv_pow, Real.norm_of_nonneg (by positivity)]
  have hb := ritt_isBigO (θ := θ) (R := max R 0) hω hωω' hdiff (by
    simpa only [comap_norm_atTop] using hrem.trans hcomp)
  simp only [comap_norm_atTop] at hb
  have hscale : (fun z : ℂ => ‖z‖ ^ (-(N : ℝ) - 1)) =O[
      cobounded ℂ ⊓ 𝓟 (rittClosedSector θ ω')] fun z : ℂ => z⁻¹ ^ (N + 1) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
    rw [one_mul, norm_pow, norm_inv, Real.norm_of_nonneg (by positivity),
      show -(N : ℝ) - 1 = -((N + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, inv_pow]
  refine (hb.trans hscale).congr' ?_ .rfl
  have hnorm := (tendsto_norm_cobounded_atTop.eventually
    (eventually_gt_atTop (max R 0))).filter_mono
      (show cobounded ℂ ⊓ 𝓟 (rittClosedSector θ ω') ≤ cobounded ℂ from inf_le_left)
  have hsec : ∀ᶠ z in cobounded ℂ ⊓ 𝓟 (rittClosedSector θ ω'), z ∈ rittClosedSector θ ω' :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ h => h)
  filter_upwards [hnorm, hsec] with z hzR hzS
  have hz0 : z ≠ 0 := norm_pos_iff.mp ((le_max_right R 0).trans_lt hzR)
  have hzmem : z ∈ rittSector θ ω R := ⟨(le_max_left R 0).trans_lt hzR, hzS.trans_lt hωω'⟩
  have hd := (han z hzmem).differentiableAt.hasDerivAt.sub (hp z hz0)
  simp only [Pi.sub_def] at hd
  rw [hd.deriv]
  simp only [smul_eq_mul]
  congr 1
  exact sum_congr rfl fun n _ => by ring

end DLMF.AsymptoticApproximations
