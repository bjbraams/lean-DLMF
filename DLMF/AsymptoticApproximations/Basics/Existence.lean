/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Basics.OrderSymbols

/-!
# Borel–Ritt existence on closed sectors and the positive axis

Every formal inverse power series is the asymptotic expansion of a function holomorphic
in a sector of opening less than `2π`, with uniform remainder bounds on its closed sector.
Restriction to the positive real axis gives the real-axis existence theorem of DLMF §2.1(iii).
-/

@[expose] public noncomputable section

open Complex Filter Set Asymptotics Bornology
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- Borel–Ritt existence with remainder estimates on a closed sector of half-opening
strictly below `π`, and holomorphy on its open part outside the unit disc. -/
@[dlmf 2.1.iii]
theorem exists_hasPoincareExpansion_closed_sector (a : ℕ → ℂ) {θ : ℝ}
    (_hθ : 0 < θ) (hθπ : θ < Real.pi) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f {z | 1 < ‖z‖ ∧ |arg z| < θ} ∧
      HasPoincareExpansion {z : ℂ | |arg z| ≤ θ} a f := by
  let ω := (θ + Real.pi) / 2
  have hθω : θ < ω := by dsimp [ω]; linarith
  have hωπ : ω ≤ Real.pi := by dsimp [ω]; linarith
  obtain ⟨f, hfd, hf⟩ := exists_hasPoincareExpansion_sector' a hωπ
  refine ⟨f, hfd.mono (fun z hz => ⟨hz.1, hz.2.trans hθω⟩), ?_⟩
  have hnorm : ∀ᶠ z in cobounded ℂ ⊓ 𝓟 {z : ℂ | |arg z| ≤ θ}, 1 < ‖z‖ :=
    (tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop 1)).filter_mono inf_le_left
  have hsec : ∀ᶠ z in cobounded ℂ ⊓ 𝓟 {z : ℂ | |arg z| ≤ θ}, |arg z| ≤ θ :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ h => h)
  have hfilter : cobounded ℂ ⊓ 𝓟 {z : ℂ | |arg z| ≤ θ} ≤
      cobounded ℂ ⊓ 𝓟 {z : ℂ | 1 < ‖z‖ ∧ |arg z| < ω} := by
    refine le_inf inf_le_left (le_principal_iff.mpr ?_)
    filter_upwards [hnorm, hsec] with z hz hs
    exact ⟨hz, hs.trans_lt hθω⟩
  exact fun N => (hf N).mono hfilter

/-- Every formal inverse power series with complex coefficients is realized asymptotically
on the positive real axis. -/
@[dlmf 2.1.iii]
theorem exists_hasAsymptoticExpansion_inv_pow_atTop (a : ℕ → ℂ) :
    ∃ f : ℝ → ℂ, HasAsymptoticExpansion atTop
      (fun n (x : ℝ) => (x : ℂ)⁻¹ ^ n) a f := by
  obtain ⟨f, _, hf⟩ := exists_hasPoincareExpansion_closed_sector a
    (θ := Real.pi / 2) (by positivity) (by linarith [Real.pi_pos])
  refine ⟨fun x => f x, hf.comp_tendsto ?_⟩
  refine tendsto_inf.mpr ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, tendsto_principal.mpr ?_⟩
  · simpa only [Complex.norm_real] using (tendsto_norm_atTop_atTop :
      Tendsto (fun x : ℝ => ‖x‖) atTop atTop)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [arg_ofReal_of_nonneg hx, abs_zero]
    positivity

end DLMF.AsymptoticApproximations
