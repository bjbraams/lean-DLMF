/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticInversion
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Exterior Laurent expansions and divergent-series obstructions

Olver, *Asymptotics and Special Functions*, Chapter 1, Theorems 7.2–7.3,
pp. 18–19, synopsis O-1.11–O-1.12. Holomorphy is on the entire deleted
neighborhood of infinity, including in the sector obstruction theorem.
-/

@[expose] public noncomputable section

open Filter Set Asymptotics PowerSeries
open scoped Topology

namespace Complex

/-- An all-argument asymptotic Laurent series converges on the entire exterior disk on which
the function is holomorphic. An arbitrary integer leading power is permitted.
Olver, Chapter 1, Theorem 7.2, synopsis O-1.11. -/
theorem hasSum_laurent_of_hasAsymptoticPowerSeries {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hf : DifferentiableOn ℂ f {z | R < ‖z‖})
    (m : ℤ) (P : ℂ⟦X⟧)
    (hP : HasAsymptoticPowerSeries (comap norm atTop) (fun z : ℂ => z⁻¹) P
      (fun z => z ^ (-m) * f z)) :
    (∀ z, R < ‖z‖ → HasSum (fun n => coeff n P * z⁻¹ ^ n) (z ^ (-m) * f z)) ∧
      SummableLocallyUniformlyOn (fun n z => coeff n P * z⁻¹ ^ n) {z | R < ‖z‖} := by
  sorry

/-- An everywhere-divergent formal expansion of a single-valued exterior holomorphic function
cannot hold uniformly over every argument; infinity is an essential singularity.
Olver, Chapter 1, Theorem 7.3, synopsis O-1.12. -/
theorem angle_lt_pi_and_not_meromorphicAt_inv_of_divergent_expansion
    {f : ℂ → ℂ} {R θ ω : ℝ} (hR : 0 ≤ R) (hω : 0 < ω)
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖}) (m : ℤ) (P : ℂ⟦X⟧)
    (hP : HasAsymptoticPowerSeries
      (comap norm atTop ⊓ 𝓟 {z | |(z * exp (-I * θ)).arg| ≤ ω})
      (fun z : ℂ => z⁻¹) P (fun z => z ^ (-m) * f z))
    (hdiv : ∀ w : ℂ, w ≠ 0 → ¬ Summable (fun n => coeff n P * w ^ n)) :
    ω < Real.pi ∧ ¬ MeromorphicAt (fun w : ℂ => f w⁻¹) 0 := by
  sorry

end Complex
