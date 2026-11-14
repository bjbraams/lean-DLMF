/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Explicit Laplace remainder majorants

Olver, *Asymptotics and Special Functions*, Chapter 3, §9, pp. 89–92,
synopsis O-3.09. For a complex exponent lambda take rho=(N+Re lambda)/mu.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Asymptotics

/-- A global exponential power majorant bounds the Laplace remainder by an exact Gamma moment.
Olver, Chapter 3, §9, synopsis O-3.09. -/
theorem integrableOn_and_norm_integral_exp_mul_le_gamma {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {R : ℝ → E} {K ρ σ x : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ) (hx : σ < x)
    (hm : AEStronglyMeasurable R (volume.restrict (Ioi 0)))
    (hR : ∀ t : ℝ, 0 < t → ‖R t‖ ≤ K * t ^ (ρ - 1) * Real.exp (σ * t)) :
    IntegrableOn (fun t => Real.exp (-x * t) • R t) (Ioi 0) ∧
      ‖∫ t in Ioi 0, Real.exp (-x * t) • R t‖ ≤
        K * Real.Gamma ρ / (x - σ) ^ ρ := by
  sorry

/-- A local majorant gives a Gamma bound plus the separately retained absolute tail.
Olver, Chapter 3, §9, synopsis O-3.09. -/
theorem norm_integral_exp_mul_le_gamma_add_tail {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {R : ℝ → E} {K ρ σ x k : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ)
    (hx : σ < x) (hk : 0 < k)
    (hi : IntegrableOn (fun t => Real.exp (-x * t) • R t) (Ioi 0))
    (hR : ∀ t ∈ Ioc 0 k, ‖R t‖ ≤ K * t ^ (ρ - 1) * Real.exp (σ * t)) :
    ‖∫ t in Ioi 0, Real.exp (-x * t) • R t‖ ≤
      K * Real.Gamma ρ / (x - σ) ^ ρ +
        ∫ t in Ioi k, Real.exp (-x * t) * ‖R t‖ := by
  sorry

/-- A separated positive phase gap yields an explicit exponentially small outer contribution.
Olver, Chapter 4, §10, synopsis O-4.13. -/
theorem integrableOn_and_norm_integral_exp_le_of_phase_gap {A E : Type*}
    [MeasurableSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure A) {S : Set A} {p : A → ℝ} {q : A → E} {x x₀ η : ℝ}
    (hp : AEStronglyMeasurable p (ν.restrict S)) (hx : x₀ ≤ x)
    (hgap : ∀ᵐ t ∂ν.restrict S, η ≤ p t)
    (hi : IntegrableOn (fun t => Real.exp (-x₀ * p t) • q t) S ν) :
    IntegrableOn (fun t => Real.exp (-x * p t) • q t) S ν ∧
      ‖∫ t in S, Real.exp (-x * p t) • q t ∂ν‖ ≤
        Real.exp (-(x - x₀) * η) * ∫ t in S, Real.exp (-x₀ * p t) * ‖q t‖ ∂ν := by
  sorry

end Asymptotics
